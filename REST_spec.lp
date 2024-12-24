require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3204727 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@REST A) s) ((@DELETE A) s ((@CHOICE A) s)))));
