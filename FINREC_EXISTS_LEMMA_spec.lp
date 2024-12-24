require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3808349 [A B] : Prf (∀ (λ f : El (fun A (fun B B)), (∀ (λ b : El B, (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (∃ (λ a : El B, (∃ (λ n : El num, ((@FINREC A B) f b s a n))))))))))));
