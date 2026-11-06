/-!
# Charter.Core.Intern — Bijective Monotonic Symbol Interning (`G1.5`, `T42`)

Maps arbitrary runtime strings (`DomId`s, entity/actor names, atom literals) to dense
`Nat` symbol IDs monotonically (`SymbolTable`), supporting open-ended runtime entity
introduction (`T42`) with kernel-checked round-trip and monotonicity proofs.
-/

namespace Charter

structure SymbolTable where
  entries : List String := []
  deriving Repr, DecidableEq, Inhabited

namespace SymbolTable

def size (t : SymbolTable) : Nat := t.entries.length

def lookupIdxAux : List String → String → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, s, i => if x == s then some i else lookupIdxAux xs s (i + 1)

def lookupId (t : SymbolTable) (s : String) : Option Nat :=
  lookupIdxAux t.entries s 0

def resolveAux : List String → Nat → Option String
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => resolveAux xs n

def resolve (t : SymbolTable) (id : Nat) : Option String :=
  resolveAux t.entries id

/-- Intern `s`, returning the existing ID if present or appending `s` at `t.size`. -/
def intern (t : SymbolTable) (s : String) : SymbolTable × Nat :=
  match t.lookupId s with
  | some id => (t, id)
  | none => ({ entries := t.entries ++ [s] }, t.entries.length)

theorem resolveAux_append_left :
    ∀ (xs : List String) (ys : List String) (n : Nat) (v : String),
      resolveAux xs n = some v → resolveAux (xs ++ ys) n = some v
  | [], _, _, _, h => by simp [resolveAux] at h
  | x :: _, _, 0, _, h => h
  | _ :: xs, ys, n + 1, v, h => resolveAux_append_left xs ys n v h

theorem resolveAux_append_end :
    ∀ (xs : List String) (s : String),
      resolveAux (xs ++ [s]) xs.length = some s
  | [], _ => rfl
  | _ :: xs, s => resolveAux_append_end xs s

theorem lookupIdxAux_sound :
    ∀ (xs : List String) (s : String) (base id : Nat),
      lookupIdxAux xs s base = some id →
      id ≥ base ∧ resolveAux xs (id - base) = some s
  | [], _, _, _, h => by simp [lookupIdxAux] at h
  | x :: xs, s, base, id, h => by
    unfold lookupIdxAux at h
    cases hxs : (x == s)
    · simp only [hxs, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hge, hres⟩ := lookupIdxAux_sound xs s (base + 1) id h
      refine ⟨by omega, ?_⟩
      have hsub : id - base = (id - (base + 1)) + 1 := by omega
      rw [hsub]
      exact hres
    · rw [hxs] at h; simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      have xeq : x = s := beq_iff_eq.mp hxs
      subst xeq
      simp [resolveAux]

/-- Interning `s` yields an ID that immediately resolves back to `s`. -/
theorem intern_resolve_self (t : SymbolTable) (s : String) :
    let (t', id) := t.intern s
    t'.resolve id = some s := by
  unfold intern resolve
  cases hl : t.lookupId s with
  | none =>
    dsimp only
    exact resolveAux_append_end t.entries s
  | some id =>
    dsimp only
    unfold lookupId at hl
    obtain ⟨_, hres⟩ := lookupIdxAux_sound t.entries s 0 id hl
    simpa using hres

/-- Interning a new string never alters the resolution of any previously assigned ID. -/
theorem intern_preserves_resolved (t : SymbolTable) (s : String) (id : Nat) (s₀ : String)
    (h : t.resolve id = some s₀) :
    (t.intern s).1.resolve id = some s₀ := by
  unfold intern resolve at *
  cases t.lookupId s with
  | some _ => exact h
  | none => exact resolveAux_append_left t.entries [s] id s₀ h

end SymbolTable

end Charter
