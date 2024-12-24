require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1059697 [A] : Prf (∀ (λ x : El (fun num (fun A bool)), (∀ (λ y : El (fun num (fun A bool)), (⇒ (= ((@_mk_rec A) x) ((@_mk_rec A) y)) (⇒ (∧ ((@ZRECSPACE A) x) ((@ZRECSPACE A) y)) (= x y)))))));
