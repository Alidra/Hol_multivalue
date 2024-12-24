require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3211605 [A] : Prf (∀ (λ s : El (fun A bool), (⇒ (¬ (= s (@EMPTY A))) ((@IN A) ((@CHOICE A) s) s))));
