# Gates need negative self-tests

Drift is what happens when a gate measures a proxy and the proxy can be met by relabeling. A gate that can be satisfied by changing a label is a defect.
Every gate ships with a negative self-test that runs in the same gate run and proves it can fail: a planted violation must be flagged, a tampered input rejected, a missing key refused. A gate without one does not land.
Gate definitions, thresholds and baselines are protected paths: editing one is a gate-defining change, judged by an attack suite that tries to pass the gate by relabeling, and it waits for the owner. Review the gates on a schedule for this exact weakness.
