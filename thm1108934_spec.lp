require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1108934 [_25719 _25727] : Prf (∧ (∀ (λ l2 : El (list _25727), (= ((@ZIP _25719 _25727) (@NIL _25719) l2) (@NIL (prod _25719 _25727))))) (∀ (λ h1' : El _25719, (∀ (λ t1 : El (list _25719), (∀ (λ l2 : El (list _25727), (= ((@ZIP _25719 _25727) ((@CONS _25719) h1' t1) l2) ((@CONS (prod _25719 _25727)) ((@̦‚ _25719 _25727) h1' ((@HD _25727) l2)) ((@ZIP _25719 _25727) t1 ((@TL _25727) l2)))))))))));
