# vbm-rng: specification

Status: to be written by the first slice item, BEFORE any Lean (hub guideline: spec first).

## What it is
Deterministic, splittable pseudo-random generators with specified streams: the same seed always gives the same bytes, and exactly reproducible sampling primitives (uniform integers in a range, uniform fractions in exact arithmetic) for simulation and experiments.

## Inputs and outputs
(bytes in, bytes out; time and randomness are inputs; no allocator across the ABI)

## Named limits
(every limit, with the harm it prevents)

## Typed refusals
(every way it refuses, each a typed value, never a default)

## Properties to prove
(one sentence per property)
