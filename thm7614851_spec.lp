require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7614851 [A B] : Prf (∧ (∀ (λ a : El (cart A B), (= ((@mk_cart A B) ((@dest_cart A B) a)) a))) (∀ (λ r : El (fun (finite_image B) A), (= T (= ((@dest_cart A B) ((@mk_cart A B) r)) r)))));
