require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem54786 [A B C] : Prf (∀ (λ P : El (fun (fun A (prod B C)) bool), (= (∃ (λ f : El (fun A (prod B C)), (P f))) (∃ (λ g : El (fun A B), (∃ (λ h : El (fun A C), (P (λ a : El A, ((@̦‚ B C) (g a) (h a)))))))))));
