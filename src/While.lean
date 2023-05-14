-- Definition of the syntax of the language
-- and the semantics of the language

-- The syntax of the language is defined using
-- inductive types.

-- The syntax of arithmetic expressions
inductive Aexp : Type
| const (n : ℤ) : Aexp
| var (x : string) : Aexp
| plus (a1 a2 : Aexp) : Aexp
| times (a1 a2 : Aexp) : Aexp

-- Notation for the syntax of arithmetic expressions
prefix ` const ` : 80 := Aexp.const
prefix ` var ` : 80 := Aexp.var
infixl ` plus ` : 65 := Aexp.plus
infixl ` times ` : 70 := Aexp.times

-- The syntax of boolean expressions
inductive Bexp : Type
| tt : Bexp
| ff : Bexp
| eq (a1 a2 : Aexp) : Bexp
| le (a1 a2 : Aexp) : Bexp
| not (b : Bexp) : Bexp
| and (b1 b2 : Bexp) : Bexp
| or (b1 b2 : Bexp) : Bexp

-- Notation for the syntax of boolean expressions
notation ` tt ` := Bexp.tt
notation ` ff ` := Bexp.ff
infix ` :≡ ` : 70 := Bexp.eq
infix ` :≤ ` : 70 := Bexp.le
prefix ` :¬ ` : 80 := Bexp.not
infix ` :∧ ` : 65 := Bexp.and
infix ` :∨ ` : 65 := Bexp.or

-- The syntax of commands
inductive Stm : Type
| skip : Stm
| assign (x : string) (a : Aexp) : Stm
| seq (S₁ S₂ : Stm) : Stm
| cond (b : Bexp) (S₁ S₂: Stm) : Stm
| while (b : Bexp) (S : Stm) : Stm

-- Notation for the syntax of commands
notation ` skip ` := Stm.skip
infix ` ::= ` : 80 := Stm.assign
infix ` ;; ` : 90 := Stm.seq
notation ` _if ` b ` _then ` c1 ` _else ` c2 ` _end ` := Stm.cond b c1 c2
notation ` _while ` b ` _do ` c ` _end ` := Stm.while b c

-- State definition
def State := string → ℤ 

def empty_state : State := λ _, 0

def update (st : State) (x : string) (n : ℤ) : State := λ x', if x' = x then n else st x'

notation st ` [ ` x ` ↦ ` n ` ] ` := update st x n


-- Denotational semantics of arithmetic expressions
@[simp] def aeval : Aexp → State → ℤ
| (const n) _ := n
| (var x) st := st x
| (a1 plus a2) st := (aeval a1 st) + (aeval a2 st)
| (a1 times a2) st := (aeval a1 st) * (aeval a2 st)

notation ` A⟦` a `⟧` := aeval a

-- Let's define some variables
def x : string := "x"
def y : string := "y"
def z : string := "z"

-- Let's see some examples of the denotational semantics of arithmetic
-- expressions.
example : A⟦(var x)⟧(empty_state[x ↦ 5]) = 5 := rfl
example : A⟦(var x)⟧(empty_state[y ↦ 5]) = 0 := rfl
example : A⟦(const 4) plus (const 7)⟧(empty_state) = 11 := rfl
example : A⟦(const 4) times (const 7)⟧(empty_state) = 28 := rfl

-- Denotational semantics of boolean expressions
@[simp] def beval : Bexp → State → bool
| (tt) _ := true
| (ff) _ := false
| (a1 :≡ a2) st := (aeval a1 st) = (aeval a2 st)
| (a1 :≤ a2) st := (aeval a1 st) ≤ (aeval a2 st)
| ( :¬ b) st := ¬ (beval b st)
| (b1 :∧ b2) st := (beval b1 st) ∧ (beval b2 st)
| (b1 :∨ b2) st := (beval b1 st) ∨ (beval b2 st)

notation ` B⟦` b `⟧` := beval b

-- Let's see some examples of the denotational semantics of boolean
-- expressions.
example : B⟦(var x :≤ const 5)⟧(empty_state[x ↦ 5]) = true := rfl
example : B⟦(var x :≤ const 5)⟧(empty_state[x ↦ 6]) = false := rfl
example : B⟦(var x :≡ const 5)⟧(empty_state[x ↦ 5]) = true := rfl
example : B⟦(var x :≡ const 5)⟧(empty_state[x ↦ 6]) = false := rfl
example : B⟦( :¬ (var x :≡ const 5))⟧(empty_state[x ↦ 5]) = false := rfl

-- Let's define some examples of Stm
example : Stm := skip
example : Stm := x ::= const 5
example : Stm := (x ::= const 5) ;; (y ::= const 6)
example : Stm := _if (var x :≡ const 5) _then (y ::= const 6) _else (z ::= const 7) _end
def loop : Stm := (x ::= const 0) ;; _while ( :¬(var x :≡ const 5)) _do skip ;; skip ;; (x ::= ((var x) plus (const 1))) _end

-- Semantics of commands.
-- We define the semantics of commands using a relation between a pair of a
-- command and a state and a state. Specifically, ceval : Stm × State → State →
-- Prop, where Stm × State is the type of pairs consisting of a command and a
-- state, State is the type of states, and Prop is the type of propositions.
-- 
-- The definition of ceval is inductive, meaning that it is defined in terms of
-- a set of inference rules. Each rule defines the conditions under which the
-- relation holds between the input pair and the output state.
-- When inductively defining propositions, lean generates the induction
-- principle for the proposition. Since inductively defined proof objects are
-- often called "derivation trees," this form of proof is also known as
-- induction on derivations. 
inductive cevalₙₛ : Stm × State → State → Prop
| assₙₛ {s x a} :
  ---------------------------------------------------------
   cevalₙₛ (x ::= a, s) (s[x ↦ A⟦a⟧s])

| skipₙₛ {s} : 
  ---------------------------------------------------------
   cevalₙₛ (skip, s) s

| compₙₛ {s s' s'' S₁ S₂}
  (hS₁ : cevalₙₛ (S₁, s) s') (hS₂ : cevalₙₛ (S₂, s') s'') :
  ---------------------------------------------------------
   cevalₙₛ (S₁ ;; S₂, s) s''

| if_ttₙₛ {s s' b S₁ S₂}
  (hcond : B⟦b⟧s = true) (hS₁ : cevalₙₛ (S₁, s) s') :
  ---------------------------------------------------------
   cevalₙₛ (_if b _then S₁ _else S₂ _end, s) s'

| if_ffₙₛ {s s' b S₁ S₂}
  (hcond : B⟦b⟧s = false) (hS₂ : cevalₙₛ (S₂, s) s') :
  ---------------------------------------------------------
   cevalₙₛ (_if b _then S₁ _else S₂ _end, s) s'

| while_ttₙₛ {s s' s'' b S}
  (hcond: B⟦b⟧s = true) (hS : cevalₙₛ (S, s) s') 
  (hW : cevalₙₛ (_while b _do S _end, s') s'') :
  ---------------------------------------------------------
   cevalₙₛ (_while b _do S _end, s) s''

| while_ffₙₛ {s b S}
  (hcond : B⟦b⟧s = false) :
  ---------------------------------------------------------
   cevalₙₛ (_while b _do S _end, s) s

infix ` ⟶ ` : 110 := cevalₙₛ

variables {S₁ S₂ : Stm} {s₀ s₁ s₂ : State}
-- #check ⟨S₁, s₀⟩ ⟶ s₁
-- #check ⟨S₁ ;; S₂, s₀⟩ ⟶ s₂

lemma beval_deterministic : ∀ {b s b₁ b₂}, B⟦b⟧s = b₁ ∧  B⟦b⟧s = b₂ → b₁ = b₂ :=
begin
  intros b s b₁ b₂ h,
  cases h with h₁ h₂,
  -- We can use the `rw` tactic to rewrite the goal using the equality
  -- `h₁` and `h₂`.
  rw h₁ at *,
  exact h₂,
end

lemma beval_tt_and_ff_false : ∀ {b s}, B⟦b⟧s = true ∧ B⟦b⟧s = false → false :=
begin
  intros b s h,
  cases h with h₁ h₂,
  rw h₁ at h₂,
  trivial,
end

lemma aeval_deterministic : ∀ {a s a₁ a₂}, A⟦a⟧s = a₁ ∧ A⟦a⟧s = a₂ → a₁ = a₂ :=
begin
  intros a s a₁ a₂ h,
  cases h with h₁ h₂,
  rw h₁ at *,
  exact h₂,
end

-- Theorem 1.1
-- Let's prove that the relation is deterministic. That is, if ⟨S, s⟩ ⟶ s₁ and
-- ⟨S, s⟩ ⟶ s₂, then s₁ = s₂.
theorem ceval_deterministic : ∀ {S s s' s''}, ⟨S, s⟩ ⟶ s' → ⟨S, s⟩ ⟶ s'' → s' = s'' :=
begin 
  -- The proof begins by introducing variables S, s₀, s₁, and s₂ and assumptions
  -- h₁ and h₂. These assumptions state that ⟨S, s₀⟩ ⟶ s₁ and ⟨S, s⟩ ⟶ s₂,
  -- meaning that S can transition from state s₀ to both s₁ and s₂.
  intros S s s' s'' h₁ h₂,

  -- The `induction h1` command starts the induction proof. This means that the
  -- proof will proceed by analyzing all possible ways that ⟨S, s⟩ ⟶ s' can be
  -- derived.
  
  -- The `generalizing s''` command tells lean to generalize the induction
  -- hypothesis, i.e instantie the induction hypothesis with an arbitrary
  -- state s''.
  induction h₁ generalizing s'',
  case cevalₙₛ.skipₙₛ : s₁ { 
    -- The `cases h2` is a case analysis on the second derivation, h2. This is
    -- because, in this case, both h1 and h2 correspond to the same rule, the
    -- cevalₙₛ.skipₙₛ rule, which means that st1 and st2 must be the same for
    -- the two derivations. The refl command completes the proof of the
    -- cevalₙₛ.skipₙₛ case by stating that the two states are equal.
    cases h₂,
    refl,
  },
  case cevalₙₛ.assₙₛ : s₁ x a { 
    -- Same as the previous case, but this time the two derivations correspond
    -- to the cevalₙₛ.assₙₛ rule.
    cases h₂,
    refl,
  },
  case cevalₙₛ.compₙₛ :  s₀ s₁ s₂ S₁ S₂ hS₁ hS₂ ih₁ ih₂ {
    cases h₂ with _ _ _ _ _ s₁' _ _ _ hS₁' hS₂', 
    have hS₁'' : s₁ = s₁',
    { exact ih₁ hS₁', },
    rw hS₁'' at ih₂,
    exact ih₂ hS₂',
  },
  case cevalₙₛ.if_ttₙₛ : s s' b S₁ S₂ hcond hS₁ ih { 
    cases h₂,
    { 
      exact ih h₂_hS₁,
    },
    { 
      -- This rule could not have been used to derive ⟨S, s⟩ ⟶ s₂, because
      -- B⟦b⟧s = false by hipothesis
      exfalso,
      exact beval_tt_and_ff_false ⟨hcond, h₂_hcond⟩,
    },
  },
  case cevalₙₛ.if_ffₙₛ : s s' b S₁ S₂ hcond hS₂ ih { 
    cases h₂,
    { 
      -- This rule could not have been used to derive ⟨S, s⟩ ⟶ s₂, because
      -- B⟦b⟧s = false by hipothesis
      exfalso,
      exact beval_tt_and_ff_false ⟨h₂_hcond, hcond⟩,
    },
    { 
      exact ih h₂_hS₂,
    },
  },
  case cevalₙₛ.while_ffₙₛ : s b S hcond { 
    cases h₂,
    { 
      -- This rule could not have been used to derive ⟨S, s⟩ ⟶ s₂, because
      -- B⟦b⟧s = false by hipothesis
      exfalso,
      exact beval_tt_and_ff_false ⟨h₂_hcond, hcond⟩,
    },
    { refl,},
  },
  case cevalₙₛ.while_ttₙₛ : s s' s'' b S hcond hS hW ihS ihW { 
    cases h₂,
    { 
      have h' : s' = h₂_s' := ihS h₂_hS,
      rw ← h' at h₂_hW,
      exact ihW h₂_hW,
    },
    { 
      -- This rule could not have been used to derive ⟨S, s⟩ ⟶ s₂, because
      -- B⟦b⟧s = false by hipothesis
      exfalso,
      exact beval_tt_and_ff_false ⟨hcond, h₂_hcond⟩,
    },
  },
end

-- Definition 1.2 (Semantic Equivalence)
def equivₙₛ (S₁ S₂ : Stm) : Prop := ∀ s s', ⟨S₁, s⟩ ⟶ s' ↔ ⟨S₂, s⟩ ⟶ s'

notation S₁ `≈ₙₛ` S₂ := equivₙₛ S₁ S₂

-- Lemma 1.3
lemma equivₙₛ_refl : ∀ S, equivₙₛ S S := 
begin
  intros S s s',
  split,
  { exact id, },
  { exact id, },
end

-- Lemma 1.4
lemma equivₙₛ_symm : ∀ S₁ S₂, equivₙₛ S₁ S₂ → equivₙₛ S₂ S₁ :=
begin
  intros S₁ S₂ h s s',
  apply iff.symm (h s s'),
end

-- Lemma 1.5
@[trans] lemma equivₙₛ_trans : ∀ S₁ S₂ S₃, equivₙₛ S₁ S₂ → equivₙₛ S₂ S₃ → equivₙₛ S₁ S₃ :=
begin
  intros S₁ S₂ S₃ h₁ h₂,
  have hL : ∀ s s', ⟨S₁, s⟩ ⟶ s' → ⟨S₃, s⟩ ⟶ s',
  { intros s s' h,
    have h' : ⟨S₂, s⟩ ⟶ s',
    { exact iff.mp (h₁ s s') h, },
    exact iff.mp (h₂ s s') h',
  },
  have hR : ∀ s s', ⟨S₃, s⟩ ⟶ s' → ⟨S₁, s⟩ ⟶ s',
  { intros s s' h,
    have h' : ⟨S₂, s⟩ ⟶ s',
    { exact iff.mpr (h₂ s s') h, },
    exact iff.mpr (h₁ s s') h',
  },
  have hLR : ∀ s s', ⟨S₁, s⟩ ⟶ s' ↔ ⟨S₃, s⟩ ⟶ s',
  { intros s s',
    split,
    { exact hL s s', },
    { exact hR s s', },
  },
  exact hLR,
end

-- Lemma 1.6
lemma equivₙₛ_skip : ∀ S, equivₙₛ (skip ;; S) S :=
begin
  intros S s s',
  split,
  { 
    intro h,
    cases h,
    have h' : s = h_s' := 
    begin
      cases h_hS₁,
      refl,
    end,
    rwa ← h' at *,
  },
  { 
    intro h,
    have h' : ⟨skip, s⟩ ⟶ s :=
    begin
      apply cevalₙₛ.skipₙₛ,
    end,
    apply cevalₙₛ.compₙₛ,
    repeat {assumption},
  },
end

-- Lemma 1.7
lemma equivₙₛ_seq_assoc : ∀ S₁ S₂ S₃, equivₙₛ ((S₁ ;; S₂) ;; S₃) (S₁ ;; (S₂ ;; S₃)) :=
begin
  intros S₁ S₂ S₃ s s',
  split,
  { 
    intro h,
    cases h,
    cases h_hS₁,
    have h' : ⟨S₂ ;; S₃, h_hS₁_s'⟩ ⟶ s' :=
    begin
      apply cevalₙₛ.compₙₛ,
      repeat {assumption},
    end,
      apply cevalₙₛ.compₙₛ,
      repeat {assumption},
  },
  { 
    intro h,
    cases h,
    cases h_hS₂,
    have h' : ⟨S₁ ;; S₂, s⟩ ⟶ h_hS₂_s' :=
    begin
      apply cevalₙₛ.compₙₛ,
      repeat {assumption},
    end,
    apply cevalₙₛ.compₙₛ,
    repeat {assumption},
  },
end

-- Lemma 1.8
lemma equivₙₛwhile_unfold : ∀ b S, equivₙₛ 
  (_while b _do S _end) (_if b _then (S ;; _while b _do S _end) _else skip _end) :=
begin
  intros b S s s',
  split,
  { 
    intro h,
    cases h,
    { 
      apply cevalₙₛ.if_ttₙₛ,
      { assumption, },
      { 
        apply cevalₙₛ.compₙₛ,
        repeat {assumption},
      },
    },
    { 
      apply cevalₙₛ.if_ffₙₛ,
      { 
        assumption,
      },
      { 
        apply cevalₙₛ.skipₙₛ,
      },
    },
  },
  { 
    intro h,
    cases h,
    { 
      cases h_hS₁,
      apply cevalₙₛ.while_ttₙₛ,
      repeat {assumption},
    },
    { 
      cases h_hS₂,
      apply cevalₙₛ.while_ffₙₛ,
      { assumption, },
    },
  },
end

-- Let's continue introducing some terminology
def terminates (S : Stm) (s : State) : Prop := ∃ s', ⟨S, s⟩ ⟶ s'
def loops (S : Stm) (s : State) : Prop := ¬ ∃ s', ⟨S, s⟩ ⟶ s'