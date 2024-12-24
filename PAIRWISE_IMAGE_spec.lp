require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4813739 [_110796 _110799] (s : El (fun _110799 bool)) : Prf (∀ (λ r : El (fun _110796 (fun _110796 bool)), (∀ (λ f : El (fun _110799 _110796), (= ((@pairwise _110796) r ((@IMAGE _110799 _110796) f s)) ((@pairwise _110799) (λ x : El _110799, (λ y : El _110799, (⇒ (¬ (= (f x) (f y))) (r (f x) (f y))))) s))))));
