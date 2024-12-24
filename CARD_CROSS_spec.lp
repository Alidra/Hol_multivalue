require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4325699 [_103797 _103799] : Prf (∀ (λ s : El (fun _103797 bool), (∀ (λ t : El (fun _103799 bool), (⇒ (∧ ((@FINITE _103797) s) ((@FINITE _103799) t)) (= ((@CARD (prod _103797 _103799)) ((@CROSS _103799 _103797) s t)) (* ((@CARD _103797) s) ((@CARD _103799) t))))))));
