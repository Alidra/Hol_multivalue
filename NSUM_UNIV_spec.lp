require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6962209 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ ((@SUBSET A) ((@support A num) + f (@UNIV A)) s) (= ((@nsum A) s f) ((@nsum A) (@UNIV A) f)))))));
