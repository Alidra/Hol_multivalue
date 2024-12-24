require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3270825 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@DIFF A) (@UNIV A) ((@DIFF A) (@UNIV A) s)) s)));
