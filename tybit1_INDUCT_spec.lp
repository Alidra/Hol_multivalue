require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7931309 [A] : Prf (∀ (λ P : El (fun (tybit1 A) bool), (⇒ (∀ (λ a : El (finite_sum (finite_sum A A) 1), (P ((@mktybit1 A) a)))) (∀ (λ x : El (tybit1 A), (P x))))));
