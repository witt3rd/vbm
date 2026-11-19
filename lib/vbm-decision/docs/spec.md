# vbm-decision: specification

Status: to be written by the first slice item, BEFORE any Lean (hub guideline: spec first).

## What it is
A typed decision-model layer: the wire contract of a decisions API (choice, noul, score and box questions), the typed answers with their probabilities, a threshold truth table that fails closed, and per-model calibration of thresholds.

## Inputs and outputs
(bytes in, bytes out; time and randomness are inputs; no allocator across the ABI)

## Named limits
(every limit, with the harm it prevents)

## Typed refusals
(every way it refuses, each a typed value, never a default)

## Properties to prove
(one sentence per property)
