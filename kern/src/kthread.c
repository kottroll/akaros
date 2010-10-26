/* Copyright (c) 2010 The Regents of the University of California
 * Barret Rhoden <brho@cs.berkeley.edu>
 * See LICENSE for details.
 *
 * Kernel threading.  These are for blocking within the kernel for whatever
 * reason, usually during blocking IO operations. */

#include <kthread.h>
#include <slab.h>
#include <page_alloc.h>
#include <pmap.h>
#include <smp.h>
#include <schedule.h>

struct kmem_cache *kthread_kcache;

void kthread_init(void)
{
	kthread_kcache = kmem_cache_create("kthread", sizeof(struct kthread),
	                                   __alignof__(struct kthread), 0, 0, 0);
}

/* This downs the semaphore and suspends the current kernel context on its
 * waitqueue if there are no pending signals.  Note that the case where the
 * signal is already there is not optimized. */
void sleep_on(struct semaphore *sem)
{
	volatile bool blocking = TRUE;	/* signal to short circuit when restarting*/
	struct kthread *kthread;
	struct page *page;				/* assumption here that stacks are PGSIZE */
	register uintptr_t new_stacktop;
	int8_t irq_state = 0;
	struct per_cpu_info *pcpui = &per_cpu_info[core_id()];

	/* interrups would be messy here */
	disable_irqsave(&irq_state);
	/* Try to get the spare first.  If there is one, we'll use it (o/w, we'll
	 * get a fresh kthread.  Why we need this is more clear when we try to
	 * restart kthreads.  Having them also ought to cut down on contention.
	 * Note we do this with interrupts disabled (which protects us from
	 * concurrent modifications). */
	if (pcpui->spare) {
		kthread = pcpui->spare;
		/* we're using the spare, so we use the page the spare held */
		new_stacktop = kthread->stacktop;
		pcpui->spare = 0;
	} else {
		kthread = kmem_cache_alloc(kthread_kcache, 0);
		assert(kthread);
		assert(!kpage_alloc(&page));	/* decref'd when the kthread is freed */
		new_stacktop = (uintptr_t)page2kva(page) + PGSIZE;
	}
	/* This is the stacktop we are currently on and wish to save */
	kthread->stacktop = get_stack_top();
	/* Set the core's new default stack */
	set_stack_top(new_stacktop);
	/* The kthread needs to stay in the process context (if there is one), but
	 * we want the core (which could be a vcore) to stay in the context too.  If
	 * we want to leave, we'll need to do that in smp_idle() or elsewhere in the
	 * code. */
	kthread->proc = current;
	kthread->proc_tf = current_tf;
	if (kthread->proc)
		kref_get(&kthread->proc->kref, 1);
	/* Save the context, toggle blocking for the reactivation */
	save_kernel_tf(&kthread->context);
	if (!blocking)
		goto block_return_path;
	blocking = FALSE;					/* for when it starts back up */
	/* Down the semaphore.  We need this to be inline.  If we're sleeping, once
	 * we unlock the kthread could be started up again and can return and start
	 * trashing this function's stack, hence the weird control flow. */
	spin_lock(&sem->lock);	/* no need for irqsave, since we disabled ints */
	if (sem->nr_signals-- <= 0)
		TAILQ_INSERT_TAIL(&sem->waiters, kthread, link);
	else								/* we didn't sleep */
		goto unwind_sleep_prep;
	spin_unlock(&sem->lock);
	/* Switch to the core's default stack.  After this, don't use local
	 * variables.  TODO: we shouldn't be using new_stacktop either, can't always
	 * trust the register keyword (AFAIK). */
	set_stack_pointer(new_stacktop);
	smp_idle();
	/* smp_idle never returns */
	assert(0);
unwind_sleep_prep:
	/* We get here if we should not sleep on sem (the signal beat the sleep).
	 * Note we are not optimizing for cases where the signal won. */
	spin_unlock(&sem->lock);
	printd("Didn't sleep, unwinding...\n");
	/* Restore the core's current and default stacktop */
	current = kthread->proc;			/* arguably unnecessary */
	if (kthread->proc)
		kref_put(&kthread->proc->kref);
	set_stack_top(kthread->stacktop);
	/* Save the allocs as the spare */
	assert(!pcpui->spare);
	pcpui->spare = kthread;
	/* save the "freshly alloc'd" stack/page, not the one we came in on */
	kthread->stacktop = new_stacktop;
block_return_path:
	printd("Returning from being 'blocked'!\n");
	enable_irqsave(&irq_state);
	return;
}

/* Starts kthread on the calling core.  This does not return, and will handle
 * the details of cleaning up whatever is currently running (freeing its stack,
 * etc). */
void restart_kthread(struct kthread *kthread)
{
	struct per_cpu_info *pcpui = &per_cpu_info[core_id()];
	uintptr_t current_stacktop;
	/* Avoid messy complications.  The kthread will enable_irqsave() when it
	 * comes back up. */
	disable_irq();
	/* Free any spare, since we need ours to become the spare (since we can't
	 * free our current kthread *before* popping it, nor can we free the current
	 * stack until we pop to the kthread's stack). */
	if (pcpui->spare) {
		page_decref(kva2page((void*)kthread->stacktop - PGSIZE));
		kmem_cache_free(kthread_kcache, pcpui->spare);
	}
	current_stacktop = get_stack_top();
	/* When a kthread runs, its stack is the default kernel stack */
	set_stack_top(kthread->stacktop);
	/* Set the spare stuff (current kthread, current (not kthread) stacktop) */
	pcpui->spare = kthread;
	kthread->stacktop = current_stacktop;
	/* We need to load the new cr3 if we want another new (or no) process */
	if (current != kthread->proc) {
		if (kthread->proc)
			lcr3(kthread->proc->env_cr3);
		else
			lcr3(boot_cr3);
	}
	/* If there's a proc current already, we'll lose that ref no matter what. */
	if (current)
		kref_put(&current->kref);
	current = kthread->proc;
	if (kthread->proc_tf)
		set_current_tf(kthread->proc_tf);
	/* Finally, restart our thread */
	pop_kernel_tf(&kthread->context);
}

/* Kmsg handler to launch/run a kthread.  This must be a routine message, since
 * it does not return.  Furthermore, like all routine kmsgs that don't return,
 * this needs to handle the fact that it won't return to the given TF (which is
 * a proc's TF, since this was routine). */
void __launch_kthread(struct trapframe *tf, uint32_t srcid, void *a0, void *a1,
	                  void *a2)
{
	struct kthread *kthread = (struct kthread*)a0;
	struct proc *cur_proc = current;
	/* If there is no proc running, don't worry about not returning. */
	if (cur_proc) {
		if (cur_proc != kthread->proc) {
			/* we're running the kthread from a different proc.  For now, we
			 * can't be _M, since that would be taking away someone's vcore to
			 * process another process's work. */
			assert(cur_proc->state == PROC_RUNNING_S);
			spin_lock(&cur_proc->proc_lock);
			/* Wrap up / yield the current _S proc, which calls schedule_proc */
			__proc_yield_s(cur_proc, tf);
			spin_unlock(&cur_proc->proc_lock);
		} else {
			assert(cur_proc->state == PROC_RUNNING_M);
			/* TODO: might need to do something here, though it will depend on
			 * how we handle async local calls. */
		}

	}
	restart_kthread(kthread);
	assert(0);
}
