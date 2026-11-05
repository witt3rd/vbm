# Choose the landing mechanism

Ask three questions in order.
1. **Who else works in the repo?** Only your agents, on one machine: one lander can serialise everything, so land directly, no pull requests. People outside your control or other teams: pull requests, because that is their shared place for review and consent.
2. **Does main deploy?** If a landing is automatically a production change, landing is not decoupled from release yet: keep a merge queue and a readable record. If main is not deployed (a library, a spec, an internal tool), direct landing is fine.
3. **How slow is the gate?** Under a minute: one commit per gate run. One to five minutes: batch the gate, or use a speculative merge queue. Over five: tier the gate first; nothing downstream helps until it is fast.

Compact form: alone + not deployed + fast gate = direct to main. Shared or deployed = pull request through a queue. Slow gate = tier it first.
