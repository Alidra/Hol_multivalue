require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7125050 [A] : Prf (∀ (λ f : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ ((@SUBSET A) ((@support A real) real_add f (@UNIV A)) s) (= ((@sum A) s f) ((@sum A) (@UNIV A) f)))))));
