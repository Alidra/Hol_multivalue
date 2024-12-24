require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem15386 [A] : Prf (∀ (λ a : El A, (∀ (λ b : El A, (∃ (λ f : El (fun bool A), (∧ (= (f F) a) (= (f T) b))))))));
