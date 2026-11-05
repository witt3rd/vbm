# Verified by construction

Write the control logic first as a specification in a proof assistant and prove its properties there. The running system is that specification, extracted or mechanically translated, and nothing else.
The question to ask of any system is how much code runs that is outside your direct control and unverified, and how that boundary is handled. Keep that number as small as possible and report it on every change.

A proof is a guarantee only about what it covers. A system that is "mostly verified" is described by the part that is not: name it, size it, shrink it.
