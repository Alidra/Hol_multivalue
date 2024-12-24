require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4786967 [A] : Prf (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (∧ (= ((@set_of_list A) ((@list_of_set A) s)) s) (= ((@LENGTH A) ((@list_of_set A) s)) ((@CARD A) s))))));
