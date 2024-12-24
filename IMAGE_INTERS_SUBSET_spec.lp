require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3487336 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun (fun A bool) bool), ((@SUBSET B) ((@IMAGE A B) f ((@INTERS A) g)) ((@INTERS B) ((@IMAGE (fun A bool) (fun B bool)) ((@IMAGE A B) f) g)))))));
