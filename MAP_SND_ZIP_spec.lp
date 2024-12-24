require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1156055 [_27145 _27147] : Prf (∀ (λ l1 : El (list _27145), (∀ (λ l2 : El (list _27147), (⇒ (= ((@LENGTH _27145) l1) ((@LENGTH _27147) l2)) (= ((@MAP (prod _27145 _27147) _27147) (@SND _27145 _27147) ((@ZIP _27145 _27147) l1 l2)) l2))))));
