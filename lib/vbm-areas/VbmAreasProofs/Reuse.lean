import VbmAreas.Reuse
import VbmAreasProofs.Decide
/-! # The reuse decision: proofs (S5) -/
namespace VbmAreas

variable (cfg : Config) (mine moved : Decision) (passed : List String)

theorem mem_reused (n : String) : n ∈ (Reuse.decide cfg mine moved passed).reused ↔
    n ∈ mine.run ∧ cfg.hasSteps n = true ∧ Reuse.stands mine moved passed n = true := by
  simp only [Reuse.decide, List.mem_filter, and_assoc]

theorem mem_rerun (n : String) : n ∈ (Reuse.decide cfg mine moved passed).rerun ↔
    n ∈ mine.run ∧ cfg.hasSteps n = true ∧ Reuse.stands mine moved passed n = false := by
  simp only [Reuse.decide, List.mem_filter, Bool.not_eq_true', and_assoc]

theorem stands_iff (n : String) : Reuse.stands mine moved passed n = true ↔
    mine.full = false ∧ moved.full = false ∧ n ∈ passed ∧ n ∉ moved.touched := by
  simp [Reuse.stands, Bool.and_eq_true, and_assoc]

/-- An area that `moved` touches is never reused: rules out a verdict kept over a path that changed under it. -/
theorem touched_not_reused (n : String) (h : n ∈ moved.touched) : n ∉ (Reuse.decide cfg mine moved passed).reused := by
  rw [mem_reused, stands_iff]; grind

/-- When `mine` is full nothing is reused: rules out reusing a verdict of a landing that ran everything for a reason. -/
theorem mine_full_nothing (h : mine.full = true) : (Reuse.decide cfg mine moved passed).reused = [] := by
  apply List.eq_nil_iff_forall_not_mem.2; intro n hn
  rw [mem_reused, stands_iff] at hn; simp [h] at hn

/-- When `moved` is full nothing of mine is reused and everything of mine that ran and has steps runs again: rules out reuse across an unmapped or gate-defining trunk change. -/
theorem moved_full_all_rerun (h : moved.full = true) :
    (Reuse.decide cfg mine moved passed).reused = [] ∧ ∀ n, n ∈ (Reuse.decide cfg mine moved passed).rerun ↔ n ∈ mine.run ∧ cfg.hasSteps n = true := by
  refine ⟨?_, fun n => ?_⟩
  · apply List.eq_nil_iff_forall_not_mem.2; intro n hn
    rw [mem_reused, stands_iff] at hn; simp [h] at hn
  · rw [mem_rerun]
    have : Reuse.stands mine moved passed n = false := by simp [Reuse.stands, h]
    simp [this]

/-- A stepless area (one with no steps, `inert` included) is neither reused nor re-run. -/
theorem stepless_neither (n : String) (h : cfg.hasSteps n = false) :
    n ∉ (Reuse.decide cfg mine moved passed).reused ∧ n ∉ (Reuse.decide cfg mine moved passed).rerun := by
  rw [mem_reused, mem_rerun]; simp [h]

/-- Reused and re-run are disjoint: rules out an area both kept and run again. -/
theorem disjoint (n : String) : n ∈ (Reuse.decide cfg mine moved passed).reused → n ∉ (Reuse.decide cfg mine moved passed).rerun := by
  rw [mem_reused, mem_rerun]; intro ⟨_, _, h⟩ ⟨_, _, h'⟩; rw [h] at h'; cases h'

/-- Together they are exactly the areas of mine that ran and have steps: no such area is dropped, none is invented. -/
theorem reused_or_rerun (n : String) : (n ∈ (Reuse.decide cfg mine moved passed).reused ∨ n ∈ (Reuse.decide cfg mine moved passed).rerun) ↔
    n ∈ mine.run ∧ cfg.hasSteps n = true := by
  rw [mem_reused, mem_rerun]
  cases Reuse.stands mine moved passed n <;> simp

/-- Only a passed area is reused; an area that did not pass runs again (fails toward running). -/
theorem reused_passed (n : String) (h : n ∈ (Reuse.decide cfg mine moved passed).reused) : n ∈ passed ∧ n ∈ mine.run ∧ cfg.hasSteps n = true := by
  rw [mem_reused, stands_iff] at h; grind

theorem unpassed_rerun (n : String) (hr : n ∈ mine.run) (hs : cfg.hasSteps n = true) (h : n ∉ passed) :
    n ∈ (Reuse.decide cfg mine moved passed).rerun := by
  rw [mem_rerun]
  have : Reuse.stands mine moved passed n = false := by
    cases e : Reuse.stands mine moved passed n
    · rfl
    · rw [stands_iff] at e; exact absurd e.2.2.1 h
  exact ⟨hr, hs, this⟩

/-- The areas with steps are the declared ones whose steps are not empty. -/
theorem hasSteps_iff (n : String) : cfg.hasSteps n = true ↔ ∃ a ∈ cfg.file.areas, a.name = n ∧ a.steps ≠ [] := by
  simp [Config.hasSteps, List.any_eq_true, Bool.and_eq_true]

/-! ## Soundness, under a stated model

A verdict is a function of the contents of the paths. The hypothesis `Reads`: the steps of an area read only the paths it owns, so its verdict is a function of the contents of those paths. -/

/-- The model of soundness: the verdict `v` of area `a` depends only on the contents of the paths `a` owns. -/
def Reads {α : Type} (a : Area) (v : (String → α) → Bool) : Prop :=
  ∀ w w' : String → α, (∀ p, a.owns p = true → w p = w' p) → v w = v w'

/-- Reuse is sound under `Reads`: if the contents on the new base differ from the old only at paths the trunk's changes `cs` name (rename ends included),
the area is in `reused`, it passed on the old base, and the verdicts of mine's areas read only owned paths, then it passes on the new base.
Rules out a reused verdict that depends on a path the trunk changed. -/
theorem reuse_sound {α : Type} (f : Areas) (hf : cfg.areas = some f) (cs : List Change) (rc : Bool) (mine : Decision) (passed : List String)
    (verdict : String → (String → α) → Bool) (hr : ∀ a ∈ f.file.areas, Reads a (verdict a.name))
    (w1 w2 : String → α) (hp : ∀ n, n ∈ passed → verdict n w1 = true)
    (hd : ∀ p, w1 p ≠ w2 p → ∃ ch ∈ cs, ∃ c ∈ ch.split, c.path = p)
    (a : Area) (ha : a ∈ f.file.areas) (hre : a.name ∈ (Reuse.decide cfg mine (cfg.decide cs rc) passed).reused) :
    verdict a.name w2 = true := by
  have hnt := touched_not_reused cfg mine (cfg.decide cs rc) passed a.name
  have hpass := (reused_passed cfg mine (cfg.decide cs rc) passed a.name hre).1
  have hsame : verdict a.name w1 = verdict a.name w2 := by
    apply hr a ha
    intro p hown
    refine Classical.byContradiction fun hne => ?_
    obtain ⟨ch, hch, c, hc, hcp⟩ := hd p hne
    have := owned_touched_file cfg cs rc f hf ch hch c hc a ha (by rw [hcp]; exact hown)
    exact hnt this hre
  rw [← hsame]; exact hp _ hpass

/-! ## Worked cases -/

private def core : Area := ⟨"core", ["core/*.py"], [], [⟨"make test", none⟩]⟩
private def docs : Area := ⟨"docs", ["docs/*.md"], [], []⟩
private def lib : Area := ⟨"lib", ["lib/*"], [], [⟨"make lib", none⟩]⟩
private def cfg1 : Config := ⟨some ⟨⟨1, [core, docs, lib]⟩, by decide +kernel⟩, [], [], []⟩
private def mineD : Decision := cfg1.decide [⟨.modified, "core/a.py", none⟩, ⟨.modified, "docs/a.md", none⟩, ⟨.modified, "lib/x", none⟩] false
private def movedD (p : String) : Decision := cfg1.decide [⟨.modified, p, none⟩] false

-- non-vacuity: core and lib passed; the trunk touched lib only: core is reused, lib runs again, docs (no steps) is neither.
example : Reuse.decide cfg1 mineD (movedD "lib/y") ["core", "lib", "docs"] = ⟨["core"], ["lib"]⟩ := by decide +kernel
-- the trunk moved a path no area owns or encloses: everything runs again.
example : Reuse.decide cfg1 mineD (movedD "notes.txt") ["core", "lib"] = ⟨[], ["core", "lib"]⟩ := by decide +kernel
-- a full mine reuses nothing; a failed area runs again.
example : (Reuse.decide cfg1 (cfg1.decide [] true) (movedD "lib/y") ["core", "lib"]).reused = [] := by decide +kernel
example : Reuse.decide cfg1 mineD (movedD "docs/b.md") ["lib"] = ⟨["lib"], ["core"]⟩ := by decide +kernel
-- an area that no change owns is not in mine and so not in the outcome.
example : Reuse.decide cfg1 (cfg1.decide [⟨.modified, "lib/x", none⟩] false) (movedD "lib/y") ["lib"] = ⟨[], ["lib"]⟩ := by decide +kernel

-- non-vacuity of `reuse_sound`: the verdict of `core` reads only `core/a.py`, an owned path, so `Reads` holds; the area is reused; the hypotheses are met.
private def vCore (w : String → Nat) : Bool := w "core/a.py" == 1
example : Reads core vCore := by
  intro w w' h
  have : w "core/a.py" = w' "core/a.py" := h _ (by decide +kernel)
  simp [vCore, this]
example : "core" ∈ (Reuse.decide cfg1 mineD (movedD "lib/y") ["core", "lib"]).reused := by decide +kernel
example : ∀ p, (fun _ => (0 : Nat)) p ≠ (fun q => if q = "lib/y" then 1 else 0) p → ∃ ch ∈ [Change.mk .modified "lib/y" none], ∃ c ∈ ch.split, c.path = p := by
  intro p h
  have hp : p = "lib/y" := by
    refine Classical.byContradiction fun hne => h ?_
    simp [hne]
  exact ⟨⟨.modified, "lib/y", none⟩, by simp, ⟨.modified, "lib/y", none⟩, by simp [Change.split], hp.symm⟩

end VbmAreas
