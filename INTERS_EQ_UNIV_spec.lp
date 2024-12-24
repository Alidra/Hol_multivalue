require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3363571 [A] : Prf (∀ (λ f : El (fun (fun A bool) bool), (= (= ((@INTERS A) f) (@UNIV A)) (∀ (λ s : El (fun A bool), (⇒ ((@IN (fun A bool)) s f) (= s (@UNIV A))))))));
