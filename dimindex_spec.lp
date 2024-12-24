require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7590231 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@dimindex A) s) ((@COND num) ((@FINITE A) (@UNIV A)) ((@CARD A) (@UNIV A)) (NUMERAL (BIT1 _0))))));
