// The kernel is a freestanding staticlib; exercise its hardware-independent
// trace buffer in the backend's host-test harness.
#[path = "../../fl4-kernel/src/trace.rs"]
mod trace;

#[test]
fn concurrent_writers_and_panic_snapshots_never_tear_entries() {
    use std::sync::Arc;
    use std::thread;
    let trace = Arc::new(trace::Trace::<128>::new());
    let workers: Vec<_> = (1..=4).map(|cpu| {
        let trace = Arc::clone(&trace);
        thread::spawn(move || {
            for n in 1..=2000 {
                trace.record([cpu * 10000 + n; 8]);
                trace.visit_recent(64, |_, e| assert!(e.iter().all(|v| *v == e[0])));
            }
        })
    }).collect();
    for worker in workers { worker.join().unwrap(); }
    assert!(trace.visit_recent(1, |_, e| assert_ne!(e, [0; 8])));
}
