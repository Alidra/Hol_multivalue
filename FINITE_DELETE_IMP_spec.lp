require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3609207 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ x : El A, (⇒ ((@FINITE A) s) ((@FINITE A) ((@DELETE A) s x)))))));
