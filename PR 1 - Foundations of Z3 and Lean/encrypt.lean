abbrev BV256 : Type := BitVec 256

-- The following theorem specifies that two bit vectors (of length 256) are equal
-- if all their bits are equal. In particular, if for every index less than 256,
-- The bit x[i] : Bool is equal to y[i] : Bool, then x is equal to y
theorem BV256.eq_of_getElem_eq {x y: BV256} : (∀ (i:Nat) (hi: i<256), x[i] = y[i]) → x = y := by
  intro h
  apply BitVec.eq_of_getLsbD_eq
  intro i
  apply h i

-- We can use the above theorem where, for instance, the simp set contains lemmas
-- about Bool that do not exist for BV256.
theorem BV256.and_not_self : ∀  (x : BV256), x &&& ~~~x = (0#256) := by
  intro x
  apply BV256.eq_of_getElem_eq
  simp

-- As above, we can easily prove the De Morgan laws on the BV256 type by
-- using the BV256.eq_of_getElem_eq theorem and the fact that these laws hold
-- for Bool values
theorem BV256.demorgan₁ {a b : BV256} : ~~~(a &&& b) = ~~~a ||| ~~~b := by
apply BV256.eq_of_getElem_eq
intro i hi
simp

theorem BV256.demorgan₂ {a b : BV256} : ~~~(a ||| b) = ~~~a &&& ~~~b := by
  apply BV256.eq_of_getElem_eq
  intro i hi
  simp

def BV256.nand (a b : BV256) : BV256 :=
  ~~~ (a &&& b)

def BV256.xor (a b: BV256) : BV256 :=
  (a.nand (a.nand b)).nand (b.nand (a.nand b))


def encrypt (message key : BV256) : BV256 :=
  message.xor key

def decrypt (cyphertext key: BV256) : BV256 :=
  cyphertext.xor key

-- Hint: you may need the BV256.demorgan₁ theorem
theorem xor_identity {a : BV256} : a.xor (0#256) = a := by
  unfold BV256.xor BV256.nand
  apply BV256.eq_of_getElem_eq
  intro i hi
  cases a[i] <;> simp

-- Hint: you may need the BV256.and_not_self theorem
theorem xor_self {a : BV256} : (a.xor a) = (0#256) := by
  unfold BV256.xor BV256.nand
  apply BV256.eq_of_getElem_eq
  intro i hi
  cases a[i] <;> simp

-- Hint: you may need the BV256.demorgan₁, BV256.demorgan₂ theorems
-- Hint 2: when working with booleans, e.g., if you apply BV256.eq_of_getElem_eq,
-- you may want to do case analysis on the value instead of applying
-- algebraic transformations. If a[i] is a bool, the tactic
-- cases a[i] will generate two goals, respectively where a[i] is true or false.
-- If you want to case split on multiple variables you can compose
-- cases tactics with the <;> operator: For instance,
-- cases a[i] <;> cases b[i] will generate 4 goal, one for each combination
-- of bool assignments to a[i] and b[i]
theorem xor_assoc {a b c : BV256} : (a.xor b).xor c = a.xor (b.xor c) := by
  unfold BV256.xor BV256.nand
  apply BV256.eq_of_getElem_eq
  intro i hi
  cases a[i] <;> cases b[i] <;> cases c[i] <;> simp

-- Hint: you may need to use the above theorems about xor
-- Avoid using the simp tactic in this proof.
theorem encrypt_correct : ∀ message key, decrypt (encrypt message key) key = message := by
  intros message key
  unfold encrypt decrypt
  rw [xor_assoc, xor_self, xor_identity]
