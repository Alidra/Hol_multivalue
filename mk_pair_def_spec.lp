require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem44172 [A B] : Prf (∀ (λ x : El A, (∀ (λ y : El B, (= ((@mk_pair A B) x y) (λ a : El A, (λ b : El B, (∧ (= a x) (= b y)))))))));
