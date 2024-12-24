require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4325462 [_103746 _103749] : Prf (∀ (λ s : El (fun _103746 bool), (∀ (λ t : El (fun _103749 bool), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ ((@HAS_SIZE _103746) s m) ((@HAS_SIZE _103749) t n)) ((@HAS_SIZE (prod _103746 _103749)) ((@CROSS _103749 _103746) s t) (* m n)))))))))));
