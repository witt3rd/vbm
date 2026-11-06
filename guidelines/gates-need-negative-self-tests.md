# Gates need negative self-tests

Drift is what happens when a gate measures a proxy and the proxy can be met by relabeling. A gate that can be satisfied by changing a label is a defect.
Every gate ships with a negative self-test that runs in the same gate run and proves it can fail: a planted violation must be flagged, a tampered input rejected, a missing key refused. A gate without one does not land.
A gate, a threshold or a baseline is never changed to make a number pass; a change to one lands like any other change, when the tests pass. Review the gates on a schedule for this exact weakness.
