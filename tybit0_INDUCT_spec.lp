require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7927982 [A] : Prf (∀ (λ P : El (fun (tybit0 A) bool), (⇒ (∀ (λ a : El (finite_sum A A), (P ((@mktybit0 A) a)))) (∀ (λ x : El (tybit0 A), (P x))))));
