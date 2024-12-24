require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4794393 [_110510] : Prf (∀ (λ s : El (fun _110510 bool), (∀ (λ r : El (fun _110510 (fun _110510 bool)), (= ((@pairwise _110510) r s) (∀ (λ x : El _110510, (∀ (λ y : El _110510, (⇒ (∧ ((@IN _110510) x s) (∧ ((@IN _110510) y s) (¬ (= x y)))) (r x y)))))))))));
