require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1155429 [_27114 _27116] : Prf (∀ (λ l1 : El (list _27114), (∀ (λ l2 : El (list _27116), (⇒ (= ((@LENGTH _27114) l1) ((@LENGTH _27116) l2)) (= ((@MAP (prod _27114 _27116) _27114) (@FST _27114 _27116) ((@ZIP _27114 _27116) l1 l2)) l1))))));
