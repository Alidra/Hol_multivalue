require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1061477 [A] : Prf (∀ (λ P : El (fun (recspace A) bool), (⇒ (∧ (P (@BOTTOM A)) (∀ (λ c : El num, (∀ (λ i : El A, (∀ (λ r : El (fun num (recspace A)), (⇒ (∀ (λ n : El num, (P (r n)))) (P ((@CONSTR A) c i r)))))))))) (∀ (λ x : El (recspace A), (P x))))));
