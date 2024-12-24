require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7608063 [A] : Prf (∀ (λ s : El (fun (finite_image A) bool), (∀ (λ t : El (fun A bool), (= ((@dimindex (finite_image A)) s) ((@dimindex A) t))))));
