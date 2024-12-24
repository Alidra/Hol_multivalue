require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1156624 [_27176 _27178] : Prf (∀ (λ l1 : El (list _27176), (∀ (λ l2 : El (list _27178), (⇒ (= ((@LENGTH _27176) l1) ((@LENGTH _27178) l2)) (= ((@LENGTH (prod _27176 _27178)) ((@ZIP _27176 _27178) l1 l2)) ((@LENGTH _27178) l2)))))));
