require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem55243 [A B C] : Prf (∀ (λ P : El (fun (fun A (fun B C)) bool), (= (∃ (λ f : El (fun A (fun B C)), (P f))) (∃ (λ f : El (fun B (fun A C)), (P (λ a : El A, (λ b : El B, (f b a)))))))));
