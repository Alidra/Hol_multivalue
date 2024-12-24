require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4802030 [_110654] : Prf (∀ (λ R : El (fun _110654 (fun _110654 bool)), (∀ (λ R' : El (fun _110654 (fun _110654 bool)), (∀ (λ s : El (fun _110654 bool), (= (∧ ((@pairwise _110654) R s) ((@pairwise _110654) R' s)) ((@pairwise _110654) (λ x : El _110654, (λ y : El _110654, (∧ (R x y) (R' x y)))) s))))))));
