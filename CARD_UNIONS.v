Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_UNIONS_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import CARD_UNION_EQ_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EMPTY_UNIONS_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_UNION_spec.
Require Import FINITE_UNIONS_spec.
Require Import INTER_UNIONS_spec.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import NSUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Require Import thm3322101_spec.
Require Import thm3322164_spec.
Require Import thm3324017_spec.
Require Import thm3325374_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem7059091 {_83064 : Type'} : term0 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem7059092 {_83064 : Type'} (P : type919 _83064) : term1 _83064 P.
Proof. exact (@lem7059091 _83064 P). Qed.
Lemma lem7059093 {_83064 : Type'} (P : type919 _83064) : (term1 _83064 P) = (term2 _83064 P).
Proof. exact (eq_refl (term1 _83064 P)). Qed.
Lemma lem7059094 {_83064 : Type'} (P : type919 _83064) : term2 _83064 P.
Proof. exact (EQ_MP (@lem7059093 _83064 P) (@lem7059092 _83064 P)). Qed.
Lemma lem7059095 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term3 _83064 P x.
Proof. exact (@lem7059094 _83064 P x). Qed.
Lemma lem7059096 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term3 _83064 P x) = ((term4 _83064 x P) = (term5 _83064 P x)).
Proof. exact (eq_refl (term3 _83064 P x)). Qed.
Lemma lem7059098 {_86951 : Type'} (s : type686 _86951) : term6 _86951 s.
Proof. exact (@lem3329633 _86951 s). Qed.
Lemma lem7059099 {_86951 : Type'} (s : type686 _86951) : (term6 _86951 s) = (((@UNIONS _86951 s) = (@EMPTY _86951)) = (term7 _86951 s)).
Proof. exact (eq_refl (term6 _86951 s)). Qed.
Lemma lem7059101 {_99816 : Type'} (h1 : term8 _99816) : term8 _99816.
Proof. exact (h1). Qed.
Lemma lem7059102 {_99816 : Type'} (s : _99816 -> Prop) (h1 : term8 _99816) : term9 _99816 s.
Proof. exact (@lem7059101 _99816 h1 s). Qed.
Lemma lem7059103 {_99816 : Type'} (s : _99816 -> Prop) : (term9 _99816 s) = (term10 _99816 s).
Proof. exact (eq_refl (term9 _99816 s)). Qed.
Lemma lem7059104 {_99816 : Type'} (s : _99816 -> Prop) (h1 : term8 _99816) : term10 _99816 s.
Proof. exact (EQ_MP (@lem7059103 _99816 s) (@lem7059102 _99816 s h1)). Qed.
Lemma lem7059105 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term8 _99816) : term11 _99816 s t.
Proof. exact (@lem7059104 _99816 s h1 t). Qed.
Lemma lem7059106 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term11 _99816 s t) = (term12 _99816 s t).
Proof. exact (eq_refl (term11 _99816 s t)). Qed.
Lemma lem7059107 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term8 _99816) : term12 _99816 s t.
Proof. exact (EQ_MP (@lem7059106 _99816 s t) (@lem7059105 _99816 s t h1)). Qed.
Lemma lem7059108 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term8 _99816) : term13 _99816 s t u.
Proof. exact (@lem7059107 _99816 s t h1 u). Qed.
Lemma lem7059109 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term13 _99816 s t u) = (term14 _99816 s t u).
Proof. exact (eq_refl (term13 _99816 s t u)). Qed.
Lemma lem7059110 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term8 _99816) : term14 _99816 s t u.
Proof. exact (EQ_MP (@lem7059109 _99816 s t u) (@lem7059108 _99816 s t u h1)). Qed.
Lemma lem7059111 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term15 _99816 s t u) : term15 _99816 s t u.
Proof. exact (h1). Qed.
Lemma lem7059112 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term8 _99816) (h2 : term15 _99816 s t u) : (term16 _99816 s t) = (@CARD _99816 u).
Proof. exact (@lem7059110 _99816 s t u h1 (@lem7059111 _99816 s t u h2)). Qed.
Lemma lem7059113 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term15 _99816 s t u) : term17 _99816 s t u.
Proof. exact (fun h0 : term8 _99816 => @lem7059112 _99816 s t u h0 h1). Qed.
Lemma lem7059114 {_99816 : Type'} (h1 : term8 _99816) : term8 _99816.
Proof. exact (h1). Qed.
Lemma lem7059115 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term8 _99816) (h2 : term15 _99816 s t u) : (term16 _99816 s t) = (@CARD _99816 u).
Proof. exact (@lem7059113 _99816 s t u h2 (@lem7059114 _99816 h1)). Qed.
Lemma lem7059116 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term8 _99816) : term14 _99816 s t u.
Proof. exact (fun h0 : term15 _99816 s t u => @lem7059115 _99816 s t u h1 h0). Qed.
Lemma lem7059117 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term8 _99816) : term12 _99816 s t.
Proof. exact (fun u : _99816 -> Prop => @lem7059116 _99816 s t u h1). Qed.
Lemma lem7059118 {_99816 : Type'} (s : _99816 -> Prop) (h1 : term8 _99816) : term10 _99816 s.
Proof. exact (fun t : _99816 -> Prop => @lem7059117 _99816 s t h1). Qed.
Lemma lem7059119 {_99816 : Type'} (h1 : term8 _99816) : term8 _99816.
Proof. exact (fun s : _99816 -> Prop => @lem7059118 _99816 s h1). Qed.
Lemma lem7059120 {_99816 : Type'} : term18 _99816.
Proof. exact (fun h0 : term8 _99816 => @lem7059119 _99816 h0). Qed.
Lemma lem7059121 {_99816 : Type'} : term8 _99816.
Proof. exact (@lem7059120 _99816 (@lem3848246 _99816)). Qed.
Lemma lem7059122 {_99816 : Type'} (s : _99816 -> Prop) : term9 _99816 s.
Proof. exact (@lem7059121 _99816 s). Qed.
Lemma lem7059123 {_99816 : Type'} (s : _99816 -> Prop) : (term9 _99816 s) = (term10 _99816 s).
Proof. exact (eq_refl (term9 _99816 s)). Qed.
Lemma lem7059124 {_99816 : Type'} (s : _99816 -> Prop) : term10 _99816 s.
Proof. exact (EQ_MP (@lem7059123 _99816 s) (@lem7059122 _99816 s)). Qed.
Lemma lem7059125 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : term11 _99816 s t.
Proof. exact (@lem7059124 _99816 s t). Qed.
Lemma lem7059126 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term11 _99816 s t) = (term12 _99816 s t).
Proof. exact (eq_refl (term11 _99816 s t)). Qed.
Lemma lem7059127 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : term12 _99816 s t.
Proof. exact (EQ_MP (@lem7059126 _99816 s t) (@lem7059125 _99816 s t)). Qed.
Lemma lem7059128 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : term13 _99816 s t u.
Proof. exact (@lem7059127 _99816 s t u). Qed.
Lemma lem7059129 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term13 _99816 s t u) = (term14 _99816 s t u).
Proof. exact (eq_refl (term13 _99816 s t u)). Qed.
Lemma lem7059143 {_126486 : Type'} : term19 _126486.
Proof. exact (proj1 (@lem6924916 _126486 Prop)). Qed.
Lemma lem7059144 {_126486 : Type'} (f : _126486 -> nat) : term20 _126486 f.
Proof. exact (@lem7059143 _126486 f). Qed.
Lemma lem7059145 {_126486 : Type'} (f : _126486 -> nat) : (term20 _126486 f) = ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)).
Proof. exact (eq_refl (term20 _126486 f)). Qed.
Lemma lem7059157 {A : Type'} (x : A) : term21 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem7059158 {A : Type'} (x : A) : (term21 A x) = (term22 A x).
Proof. exact (eq_refl (term21 A x)). Qed.
Lemma lem7059159 {A : Type'} (x : A) : term22 A x.
Proof. exact (EQ_MP (@lem7059158 A x) (@lem7059157 A x)). Qed.
Lemma lem7059160 {A : Type'} (x : A) (y : A) : term23 A x y.
Proof. exact (@lem7059159 A x y). Qed.
Lemma lem7059161 {A : Type'} (y : A) (x : A) : (term23 A x y) = (term24 A y x).
Proof. exact (eq_refl (term23 A x y)). Qed.
Lemma lem7059162 {A : Type'} (y : A) (x : A) : term24 A y x.
Proof. exact (EQ_MP (@lem7059161 A y x) (@lem7059160 A x y)). Qed.
Lemma lem7059163 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term25 A y x s.
Proof. exact (@lem7059162 A y x s). Qed.
Lemma lem7059164 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term25 A y x s) = ((term26 A x y s) = (term27 A y x s)).
Proof. exact (eq_refl (term25 A y x s)). Qed.
Lemma lem7059166 {A : Type'} (x : A) : term28 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem7059167 {A : Type'} (x : A) : (term28 A x) = (term29 A x).
Proof. exact (eq_refl (term28 A x)). Qed.
Lemma lem7059168 {A : Type'} (x : A) : term29 A x.
Proof. exact (EQ_MP (@lem7059167 A x) (@lem7059166 A x)). Qed.
Lemma lem7059169 {A : Type'} (x : A) : term30 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem7059171 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem7059172 {A : Type'} (P : type686 A) (h1 : term31 A) : term32 A P.
Proof. exact (@lem7059171 A h1 P). Qed.
Lemma lem7059173 {A : Type'} (P : type686 A) : (term32 A P) = (term33 A P).
Proof. exact (eq_refl (term32 A P)). Qed.
Lemma lem7059174 {A : Type'} (P : type686 A) (h1 : term31 A) : term33 A P.
Proof. exact (EQ_MP (@lem7059173 A P) (@lem7059172 A P h1)). Qed.
Lemma lem7059175 {A : Type'} (P : type686 A) (h1 : term34 A P) : term34 A P.
Proof. exact (h1). Qed.
Lemma lem7059176 {A : Type'} (P : type686 A) (h1 : term31 A) (h2 : term34 A P) : term35 A P.
Proof. exact (@lem7059174 A P h1 (@lem7059175 A P h2)). Qed.
Lemma lem7059177 {A : Type'} (P : type686 A) (h1 : term34 A P) : term36 A P.
Proof. exact (fun h0 : term31 A => @lem7059176 A P h0 h1). Qed.
Lemma lem7059178 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem7059179 {A : Type'} (P : type686 A) (h1 : term31 A) (h2 : term34 A P) : term35 A P.
Proof. exact (@lem7059177 A P h2 (@lem7059178 A h1)). Qed.
Lemma lem7059180 {A : Type'} (P : type686 A) (h1 : term31 A) : term33 A P.
Proof. exact (fun h0 : term34 A P => @lem7059179 A P h1 h0). Qed.
Lemma lem7059181 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (fun P : type686 A => @lem7059180 A P h1). Qed.
Lemma lem7059182 {A : Type'} : term37 A.
Proof. exact (fun h0 : term31 A => @lem7059181 A h0). Qed.
Lemma lem7059183 {A : Type'} : term31 A.
Proof. exact (@lem7059182 A (@lem3558722 A)). Qed.
Lemma lem7059184 {A : Type'} (P : type686 A) : term32 A P.
Proof. exact (@lem7059183 A P). Qed.
Lemma lem7059185 {A : Type'} (P : type686 A) : (term32 A P) = (term33 A P).
Proof. exact (eq_refl (term32 A P)). Qed.
Lemma lem7059192 (p : Prop) (q : Prop) (r : Prop) : (term38 p q r) = (term39 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7059193 {A : Type'} (s : type686 A) : (term40 A s) = (term41 A s).
Proof. exact (@lem7059192 (@FINITE (A -> Prop) s) (term42 A s) ((term43 A s) = (@nsum (A -> Prop) s (@CARD A)))). Qed.
Lemma lem7059194 {A : Type'} : (term44 A) = (term45 A).
Proof. exact (fun_ext (fun s : type686 A => @lem7059193 A s)). Qed.
Lemma lem7059195 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7059196 {A : Type'} : (term46 A) = (term47 A).
Proof. exact (MK_COMB (@lem7059195 A) (@lem7059194 A)). Qed.
Lemma lem7059197 {A : Type'} : (term47 A) = (term46 A).
Proof. exact (SYM (@lem7059196 A)). Qed.
Lemma lem7059199 {A : Type'} (P : type686 A) : term33 A P.
Proof. exact (EQ_MP (@lem7059185 A P) (@lem7059184 A P)). Qed.
Lemma lem7059200 {A : Type'} (P : type180 A) : term48 A P.
Proof. exact (@lem7059199 (A -> Prop) P). Qed.
Lemma lem7059201 {A : Type'} : term49 A.
Proof. exact (@lem7059200 A (term50 A)). Qed.
Lemma lem7059202 {A : Type'} : (term51 A) = (term52 A).
Proof. exact (eq_refl (term51 A)). Qed.
Lemma lem7059203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059204 {A : Type'} : (term53 A) = (term54 A).
Proof. exact (MK_COMB (@lem7059203) (@lem7059202 A)). Qed.
Lemma lem7059205 {A : Type'} (s : type686 A) : (term55 A s) = (term56 A s).
Proof. exact (eq_refl (term55 A s)). Qed.
Lemma lem7059206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059207 {A : Type'} (s : type686 A) : (term57 A s) = (term58 A s).
Proof. exact (MK_COMB (@lem7059206) (@lem7059205 A s)). Qed.
Lemma lem7059208 {A : Type'} (x : A -> Prop) (s : type686 A) : (term59 A x s) = (term59 A x s).
Proof. exact (eq_refl (term59 A x s)). Qed.
Lemma lem7059209 {A : Type'} (x : A -> Prop) (s : type686 A) : (term60 A x s) = (term61 A x s).
Proof. exact (MK_COMB (@lem7059207 A s) (@lem7059208 A x s)). Qed.
Lemma lem7059210 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7059211 {A : Type'} (x : A -> Prop) (s : type686 A) : (term62 A x s) = (term63 A x s).
Proof. exact (MK_COMB (@lem7059210) (@lem7059209 A x s)). Qed.
Lemma lem7059212 {A : Type'} (x : A -> Prop) (s : type686 A) : (term64 A x s) = (term65 A x s).
Proof. exact (eq_refl (term64 A x s)). Qed.
Lemma lem7059213 {A : Type'} (x : A -> Prop) (s : type686 A) : (term66 A x s) = (term67 A x s).
Proof. exact (MK_COMB (@lem7059211 A x s) (@lem7059212 A x s)). Qed.
Lemma lem7059214 {A : Type'} (x : A -> Prop) : (term68 A x) = (term69 A x).
Proof. exact (fun_ext (fun s : type686 A => @lem7059213 A x s)). Qed.
Lemma lem7059215 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7059216 {A : Type'} (x : A -> Prop) : (term70 A x) = (term71 A x).
Proof. exact (MK_COMB (@lem7059215 A) (@lem7059214 A x)). Qed.
Lemma lem7059217 {A : Type'} : (term72 A) = (term73 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem7059216 A x)). Qed.
Lemma lem7059218 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7059219 {A : Type'} : (term74 A) = (term75 A).
Proof. exact (MK_COMB (@lem7059218 A) (@lem7059217 A)). Qed.
Lemma lem7059220 {A : Type'} : (term76 A) = (term77 A).
Proof. exact (MK_COMB (@lem7059204 A) (@lem7059219 A)). Qed.
Lemma lem7059221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7059222 {A : Type'} : (term78 A) = (term79 A).
Proof. exact (MK_COMB (@lem7059221) (@lem7059220 A)). Qed.
Lemma lem7059223 {A : Type'} (s : type686 A) : (term55 A s) = (term56 A s).
Proof. exact (eq_refl (term55 A s)). Qed.
Lemma lem7059224 {A : Type'} (s : type686 A) : (term80 A s) = (term80 A s).
Proof. exact (eq_refl (term80 A s)). Qed.
Lemma lem7059225 {A : Type'} (s : type686 A) : (term81 A s) = (term41 A s).
Proof. exact (MK_COMB (@lem7059224 A s) (@lem7059223 A s)). Qed.
Lemma lem7059226 {A : Type'} : (term82 A) = (term45 A).
Proof. exact (fun_ext (fun s : type686 A => @lem7059225 A s)). Qed.
Lemma lem7059227 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7059228 {A : Type'} : (term83 A) = (term47 A).
Proof. exact (MK_COMB (@lem7059227 A) (@lem7059226 A)). Qed.
Lemma lem7059229 {A : Type'} : (term49 A) = (term84 A).
Proof. exact (MK_COMB (@lem7059222 A) (@lem7059228 A)). Qed.
Lemma lem7059230 {A : Type'} : term84 A.
Proof. exact (EQ_MP (@lem7059229 A) (@lem7059201 A)). Qed.
Lemma lem7059244 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7059169 A x (@lem7059168 A x)). Qed.
Lemma lem7059245 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem7059244 (A -> Prop) x). Qed.
Lemma lem7059246 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem7059245 A t). Qed.
Lemma lem7059247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7059248 {A : Type'} (t : A -> Prop) : (term85 A t) = (imp False).
Proof. exact (MK_COMB (@lem7059247) (@lem7059246 A t)). Qed.
Lemma lem7059249 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@FINITE A t).
Proof. exact (eq_refl (@FINITE A t)). Qed.
Lemma lem7059250 {A : Type'} (t : A -> Prop) : (term86 A t) = (term87 A t).
Proof. exact (MK_COMB (@lem7059248 A t) (@lem7059249 A t)). Qed.
Lemma lem7059252 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem7059253 {A : Type'} (t : A -> Prop) : (term87 A t) = True.
Proof. exact (@lem7059252 (@FINITE A t)). Qed.
Lemma lem7059254 {A : Type'} (t : A -> Prop) : (term86 A t) = True.
Proof. exact (TRANS (@lem7059250 A t) (@lem7059253 A t)). Qed.
Lemma lem7059255 {A : Type'} : (term88 A) = (term89 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7059254 A t)). Qed.
Lemma lem7059256 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7059257 {A : Type'} : (term90 A) = (term91 A).
Proof. exact (MK_COMB (@lem7059256 A) (@lem7059255 A)). Qed.
Lemma lem7059259 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7059260 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (@lem7059259 (A -> Prop) t). Qed.
Lemma lem7059261 {A : Type'} : (term91 A) = True.
Proof. exact (@lem7059260 A True). Qed.
Lemma lem7059262 {A : Type'} : (term90 A) = True.
Proof. exact (TRANS (@lem7059257 A) (@lem7059261 A)). Qed.
Lemma lem7059263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059264 {A : Type'} : (term94 A) = (and True).
Proof. exact (MK_COMB (@lem7059263) (@lem7059262 A)). Qed.
Lemma lem7059278 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7059169 A x (@lem7059168 A x)). Qed.
Lemma lem7059279 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem7059278 (A -> Prop) x). Qed.
Lemma lem7059280 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem7059279 A t). Qed.
Lemma lem7059281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059282 {A : Type'} (t : A -> Prop) : (term95 A t) = (and False).
Proof. exact (MK_COMB (@lem7059281) (@lem7059280 A t)). Qed.
Lemma lem7059286 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7059169 A x (@lem7059168 A x)). Qed.
Lemma lem7059287 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem7059286 (A -> Prop) x). Qed.
Lemma lem7059288 {A : Type'} (u : A -> Prop) : (@IN (A -> Prop) u (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem7059287 A u). Qed.
Lemma lem7059289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059290 {A : Type'} (u : A -> Prop) : (term95 A u) = (and False).
Proof. exact (MK_COMB (@lem7059289) (@lem7059288 A u)). Qed.
Lemma lem7059293 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term96 A t u) = (term96 A t u).
Proof. exact (eq_refl (term96 A t u)). Qed.
Lemma lem7059294 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term97 A t u) = (term98 A t u).
Proof. exact (MK_COMB (@lem7059290 A u) (@lem7059293 A t u)). Qed.
Lemma lem7059296 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem7059297 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term98 A t u) = False.
Proof. exact (@lem7059296 (term96 A t u)). Qed.
Lemma lem7059298 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term97 A t u) = False.
Proof. exact (TRANS (@lem7059294 A t u) (@lem7059297 A t u)). Qed.
Lemma lem7059299 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term99 A t u) = (False /\ False).
Proof. exact (MK_COMB (@lem7059282 A t) (@lem7059298 A t u)). Qed.
Lemma lem7059301 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem7059302 : (False /\ False) = False.
Proof. exact (@lem7059301 False). Qed.
Lemma lem7059303 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term99 A t u) = False.
Proof. exact (TRANS (@lem7059299 A t u) (@lem7059302)). Qed.
Lemma lem7059304 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7059305 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term100 A t u) = (imp False).
Proof. exact (MK_COMB (@lem7059304) (@lem7059303 A t u)). Qed.
Lemma lem7059308 {A : Type'} (t : A -> Prop) (u : A -> Prop) : ((@INTER A t u) = (@EMPTY A)) = ((@INTER A t u) = (@EMPTY A)).
Proof. exact (eq_refl ((@INTER A t u) = (@EMPTY A))). Qed.
Lemma lem7059309 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term101 A t u) = (term102 A t u).
Proof. exact (MK_COMB (@lem7059305 A t u) (@lem7059308 A t u)). Qed.
Lemma lem7059311 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem7059312 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term102 A t u) = True.
Proof. exact (@lem7059311 ((@INTER A t u) = (@EMPTY A))). Qed.
Lemma lem7059313 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term101 A t u) = True.
Proof. exact (TRANS (@lem7059309 A t u) (@lem7059312 A t u)). Qed.
Lemma lem7059314 {A : Type'} (t : A -> Prop) : (term103 A t) = (term89 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7059313 A t u)). Qed.
Lemma lem7059315 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7059316 {A : Type'} (t : A -> Prop) : (term104 A t) = (term91 A).
Proof. exact (MK_COMB (@lem7059315 A) (@lem7059314 A t)). Qed.
Lemma lem7059318 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7059319 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (@lem7059318 (A -> Prop) t). Qed.
Lemma lem7059320 {A : Type'} : (term91 A) = True.
Proof. exact (@lem7059319 A True). Qed.
Lemma lem7059321 {A : Type'} (t : A -> Prop) : (term104 A t) = True.
Proof. exact (TRANS (@lem7059316 A t) (@lem7059320 A)). Qed.
Lemma lem7059322 {A : Type'} : (term105 A) = (term89 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7059321 A t)). Qed.
Lemma lem7059323 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7059324 {A : Type'} : (term106 A) = (term91 A).
Proof. exact (MK_COMB (@lem7059323 A) (@lem7059322 A)). Qed.
Lemma lem7059326 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7059327 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (@lem7059326 (A -> Prop) t). Qed.
Lemma lem7059328 {A : Type'} : (term91 A) = True.
Proof. exact (@lem7059327 A True). Qed.
Lemma lem7059329 {A : Type'} : (term106 A) = True.
Proof. exact (TRANS (@lem7059324 A) (@lem7059328 A)). Qed.
Lemma lem7059330 {A : Type'} : (term107 A) = (True /\ True).
Proof. exact (MK_COMB (@lem7059264 A) (@lem7059329 A)). Qed.
Lemma lem7059332 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7059333 : (True /\ True) = True.
Proof. exact (@lem7059332 True). Qed.
Lemma lem7059334 {A : Type'} : (term107 A) = True.
Proof. exact (TRANS (@lem7059330 A) (@lem7059333)). Qed.
Lemma lem7059335 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7059336 {A : Type'} : (term108 A) = (imp True).
Proof. exact (MK_COMB (@lem7059335) (@lem7059334 A)). Qed.
Lemma lem7059340 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem7059341 {A : Type'} : (@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A).
Proof. exact (@lem7059340 A). Qed.
Lemma lem7059342 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem7059343 {A : Type'} : (term109 A) = (@CARD A (@EMPTY A)).
Proof. exact (MK_COMB (@lem7059342 A) (@lem7059341 A)). Qed.
Lemma lem7059344 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7059345 {A : Type'} : (term110 A) = (term111 A).
Proof. exact (MK_COMB (@lem7059344) (@lem7059343 A)). Qed.
Lemma lem7059346 {A : Type'} : (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A)) = (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A)).
Proof. exact (eq_refl (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A))). Qed.
Lemma lem7059347 {A : Type'} : ((term109 A) = (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A))) = ((@CARD A (@EMPTY A)) = (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A))).
Proof. exact (MK_COMB (@lem7059345 A) (@lem7059346 A)). Qed.
Lemma lem7059350 {A : Type'} : (term52 A) = (term112 A).
Proof. exact (MK_COMB (@lem7059336 A) (@lem7059347 A)). Qed.
Lemma lem7059352 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7059353 {A : Type'} : (term112 A) = ((@CARD A (@EMPTY A)) = (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A))).
Proof. exact (@lem7059352 ((@CARD A (@EMPTY A)) = (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A)))). Qed.
Lemma lem7059356 {A : Type'} : (term52 A) = ((@CARD A (@EMPTY A)) = (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A))).
Proof. exact (TRANS (@lem7059350 A) (@lem7059353 A)). Qed.
Lemma lem7059357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059358 {A : Type'} : (term54 A) = (term113 A).
Proof. exact (MK_COMB (@lem7059357) (@lem7059356 A)). Qed.
Lemma lem7059414 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term26 A x y s) = (term27 A y x s).
Proof. exact (EQ_MP (@lem7059164 A y x s) (@lem7059163 A y x s)). Qed.
Lemma lem7059415 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term114 A x y s) = (term115 A y x s).
Proof. exact (@lem7059414 (A -> Prop) y x s). Qed.
Lemma lem7059416 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : type686 A) : (term114 A t x s) = (term115 A x t s).
Proof. exact (@lem7059415 A x t s). Qed.
Lemma lem7059421 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7059422 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : type686 A) : (term116 A t x s) = (term117 A x t s).
Proof. exact (MK_COMB (@lem7059421) (@lem7059416 A x t s)). Qed.
Lemma lem7059423 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@FINITE A t).
Proof. exact (eq_refl (@FINITE A t)). Qed.
Lemma lem7059424 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) : (term118 A x s t) = (term119 A x s t).
Proof. exact (MK_COMB (@lem7059422 A x t s) (@lem7059423 A t)). Qed.
Lemma lem7059427 {A : Type'} (x : A -> Prop) (s : type686 A) : (term120 A x s) = (term121 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7059424 A x s t)). Qed.
Lemma lem7059428 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7059429 {A : Type'} (x : A -> Prop) (s : type686 A) : (term122 A x s) = (term123 A x s).
Proof. exact (MK_COMB (@lem7059428 A) (@lem7059427 A x s)). Qed.
Lemma lem7059434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059435 {A : Type'} (x : A -> Prop) (s : type686 A) : (term124 A x s) = (term125 A x s).
Proof. exact (MK_COMB (@lem7059434) (@lem7059429 A x s)). Qed.
Lemma lem7059449 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term26 A x y s) = (term27 A y x s).
Proof. exact (EQ_MP (@lem7059164 A y x s) (@lem7059163 A y x s)). Qed.
Lemma lem7059450 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term114 A x y s) = (term115 A y x s).
Proof. exact (@lem7059449 (A -> Prop) y x s). Qed.
Lemma lem7059451 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : type686 A) : (term114 A t x s) = (term115 A x t s).
Proof. exact (@lem7059450 A x t s). Qed.
Lemma lem7059456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059457 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : type686 A) : (term126 A t x s) = (term127 A x t s).
Proof. exact (MK_COMB (@lem7059456) (@lem7059451 A x t s)). Qed.
Lemma lem7059461 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term26 A x y s) = (term27 A y x s).
Proof. exact (EQ_MP (@lem7059164 A y x s) (@lem7059163 A y x s)). Qed.
Lemma lem7059462 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term114 A x y s) = (term115 A y x s).
Proof. exact (@lem7059461 (A -> Prop) y x s). Qed.
Lemma lem7059463 {A : Type'} (x : A -> Prop) (u : A -> Prop) (s : type686 A) : (term114 A u x s) = (term115 A x u s).
Proof. exact (@lem7059462 A x u s). Qed.
Lemma lem7059468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059469 {A : Type'} (x : A -> Prop) (u : A -> Prop) (s : type686 A) : (term126 A u x s) = (term127 A x u s).
Proof. exact (MK_COMB (@lem7059468) (@lem7059463 A x u s)). Qed.
Lemma lem7059472 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term96 A t u) = (term96 A t u).
Proof. exact (eq_refl (term96 A t u)). Qed.
Lemma lem7059473 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (u : A -> Prop) : (term128 A x s t u) = (term129 A x s t u).
Proof. exact (MK_COMB (@lem7059469 A x u s) (@lem7059472 A t u)). Qed.
Lemma lem7059476 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (u : A -> Prop) : (term130 A x s t u) = (term131 A x s t u).
Proof. exact (MK_COMB (@lem7059457 A x t s) (@lem7059473 A x s t u)). Qed.
Lemma lem7059479 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7059480 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (u : A -> Prop) : (term132 A x s t u) = (term133 A x s t u).
Proof. exact (MK_COMB (@lem7059479) (@lem7059476 A x s t u)). Qed.
Lemma lem7059483 {A : Type'} (t : A -> Prop) (u : A -> Prop) : ((@INTER A t u) = (@EMPTY A)) = ((@INTER A t u) = (@EMPTY A)).
Proof. exact (eq_refl ((@INTER A t u) = (@EMPTY A))). Qed.
Lemma lem7059484 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (u : A -> Prop) : (term134 A x s t u) = (term135 A x s t u).
Proof. exact (MK_COMB (@lem7059480 A x s t u) (@lem7059483 A t u)). Qed.
Lemma lem7059487 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) : (term136 A x s t) = (term137 A x s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7059484 A x s t u)). Qed.
Lemma lem7059488 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7059489 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) : (term138 A x s t) = (term139 A x s t).
Proof. exact (MK_COMB (@lem7059488 A) (@lem7059487 A x s t)). Qed.
Lemma lem7059494 {A : Type'} (x : A -> Prop) (s : type686 A) : (term140 A x s) = (term141 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7059489 A x s t)). Qed.
Lemma lem7059495 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7059496 {A : Type'} (x : A -> Prop) (s : type686 A) : (term142 A x s) = (term143 A x s).
Proof. exact (MK_COMB (@lem7059495 A) (@lem7059494 A x s)). Qed.
Lemma lem7059501 {A : Type'} (x : A -> Prop) (s : type686 A) : (term144 A x s) = (term145 A x s).
Proof. exact (MK_COMB (@lem7059435 A x s) (@lem7059496 A x s)). Qed.
Lemma lem7059504 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7059505 {A : Type'} (x : A -> Prop) (s : type686 A) : (term146 A x s) = (term147 A x s).
Proof. exact (MK_COMB (@lem7059504) (@lem7059501 A x s)). Qed.
Lemma lem7059509 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term148 _86841 s u) = (term149 _86841 s u).
Proof. exact (EQ_MP (@lem3324017 _86841 s u) (@lem3325374 _86841 s u)). Qed.
Lemma lem7059510 {A : Type'} (s : A -> Prop) (u : type686 A) : (term148 A s u) = (term149 A s u).
Proof. exact (@lem7059509 A s u). Qed.
Lemma lem7059511 {A : Type'} (x : A -> Prop) (s : type686 A) : (term148 A x s) = (term149 A x s).
Proof. exact (@lem7059510 A x s). Qed.
Lemma lem7059512 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem7059513 {A : Type'} (x : A -> Prop) (s : type686 A) : (term150 A x s) = (term151 A x s).
Proof. exact (MK_COMB (@lem7059512 A) (@lem7059511 A x s)). Qed.
Lemma lem7059514 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7059515 {A : Type'} (x : A -> Prop) (s : type686 A) : (term152 A x s) = (term153 A x s).
Proof. exact (MK_COMB (@lem7059514) (@lem7059513 A x s)). Qed.
Lemma lem7059516 {A : Type'} (x : A -> Prop) (s : type686 A) : (term154 A x s) = (term154 A x s).
Proof. exact (eq_refl (term154 A x s)). Qed.
Lemma lem7059517 {A : Type'} (x : A -> Prop) (s : type686 A) : ((term150 A x s) = (term154 A x s)) = ((term151 A x s) = (term154 A x s)).
Proof. exact (MK_COMB (@lem7059515 A x s) (@lem7059516 A x s)). Qed.
Lemma lem7059520 {A : Type'} (x : A -> Prop) (s : type686 A) : (term65 A x s) = (term155 A x s).
Proof. exact (MK_COMB (@lem7059505 A x s) (@lem7059517 A x s)). Qed.
Lemma lem7059523 {A : Type'} (x : A -> Prop) (s : type686 A) : (term63 A x s) = (term63 A x s).
Proof. exact (eq_refl (term63 A x s)). Qed.
Lemma lem7059524 {A : Type'} (x : A -> Prop) (s : type686 A) : (term67 A x s) = (term156 A x s).
Proof. exact (MK_COMB (@lem7059523 A x s) (@lem7059520 A x s)). Qed.
Lemma lem7059527 {A : Type'} (x : A -> Prop) : (term69 A x) = (term157 A x).
Proof. exact (fun_ext (fun s : type686 A => @lem7059524 A x s)). Qed.
Lemma lem7059528 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7059529 {A : Type'} (x : A -> Prop) : (term71 A x) = (term158 A x).
Proof. exact (MK_COMB (@lem7059528 A) (@lem7059527 A x)). Qed.
Lemma lem7059534 {A : Type'} : (term73 A) = (term159 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem7059529 A x)). Qed.
Lemma lem7059535 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7059536 {A : Type'} : (term75 A) = (term160 A).
Proof. exact (MK_COMB (@lem7059535 A) (@lem7059534 A)). Qed.
Lemma lem7059541 {A : Type'} : (term77 A) = (term161 A).
Proof. exact (MK_COMB (@lem7059358 A) (@lem7059536 A)). Qed.
Lemma lem7059544 {A : Type'} : (term161 A) = (term77 A).
Proof. exact (SYM (@lem7059541 A)). Qed.
Lemma lem7059550 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem7059551 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7059552 {A : Type'} : (term111 A) = term162.
Proof. exact (MK_COMB (@lem7059551) (@lem7059550 A)). Qed.
Lemma lem7059554 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem7059145 _126486 f) (@lem7059144 _126486 f)). Qed.
Lemma lem7059555 {A : Type'} (f : type687 A) : (@nsum (A -> Prop) (@EMPTY (A -> Prop)) f) = (NUMERAL 0).
Proof. exact (@lem7059554 (A -> Prop) f). Qed.
Lemma lem7059556 {A : Type'} : (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A)) = (NUMERAL 0).
Proof. exact (@lem7059555 A (@CARD A)). Qed.
Lemma lem7059557 {A : Type'} : ((@CARD A (@EMPTY A)) = (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem7059552 A) (@lem7059556 A)). Qed.
Lemma lem7059559 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7059560 (x : nat) : (x = x) = True.
Proof. exact (@lem7059559 nat x). Qed.
Lemma lem7059561 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem7059560 (NUMERAL 0)). Qed.
Lemma lem7059562 {A : Type'} : ((@CARD A (@EMPTY A)) = (@nsum (A -> Prop) (@EMPTY (A -> Prop)) (@CARD A))) = True.
Proof. exact (TRANS (@lem7059557 A) (@lem7059561)). Qed.
Lemma lem7059563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059564 {A : Type'} : (term113 A) = (and True).
Proof. exact (MK_COMB (@lem7059563) (@lem7059562 A)). Qed.
Lemma lem7059651 {A : Type'} : (term160 A) = (term160 A).
Proof. exact (eq_refl (term160 A)). Qed.
Lemma lem7059652 {A : Type'} : (term161 A) = (term163 A).
Proof. exact (MK_COMB (@lem7059564 A) (@lem7059651 A)). Qed.
Lemma lem7059654 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7059655 {A : Type'} : (term163 A) = (term160 A).
Proof. exact (@lem7059654 (term160 A)). Qed.
Lemma lem7059742 {A : Type'} : (term161 A) = (term160 A).
Proof. exact (TRANS (@lem7059652 A) (@lem7059655 A)). Qed.
Lemma lem7059743 {A : Type'} : (term160 A) = (term161 A).
Proof. exact (SYM (@lem7059742 A)). Qed.
Lemma lem7059744 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term61 A t f) : term61 A t f.
Proof. exact (h1). Qed.
Lemma lem7059745 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term145 A t f) : term145 A t f.
Proof. exact (h1). Qed.
Lemma lem7059746 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term143 A t f.
Proof. exact (h1). Qed.
Lemma lem7059747 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term123 A t f.
Proof. exact (h1). Qed.
Lemma lem7059748 {_126525 : Type'} : term164 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem7059749 {_126525 : Type'} (x : _126525) : term165 _126525 x.
Proof. exact (@lem7059748 _126525 x). Qed.
Lemma lem7059750 {_126525 : Type'} (x : _126525) : (term165 _126525 x) = (term166 _126525 x).
Proof. exact (eq_refl (term165 _126525 x)). Qed.
Lemma lem7059751 {_126525 : Type'} (x : _126525) : term166 _126525 x.
Proof. exact (EQ_MP (@lem7059750 _126525 x) (@lem7059749 _126525 x)). Qed.
Lemma lem7059752 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term167 _126525 x f.
Proof. exact (@lem7059751 _126525 x f). Qed.
Lemma lem7059753 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term167 _126525 x f) = (term168 _126525 x f).
Proof. exact (eq_refl (term167 _126525 x f)). Qed.
Lemma lem7059754 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term168 _126525 x f.
Proof. exact (EQ_MP (@lem7059753 _126525 x f) (@lem7059752 _126525 x f)). Qed.
Lemma lem7059755 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term169 _126525 x f s.
Proof. exact (@lem7059754 _126525 x f s). Qed.
Lemma lem7059756 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term169 _126525 x f s) = (term170 _126525 x s f).
Proof. exact (eq_refl (term169 _126525 x f s)). Qed.
Lemma lem7059757 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term170 _126525 x s f.
Proof. exact (EQ_MP (@lem7059756 _126525 x s f) (@lem7059755 _126525 x f s)). Qed.
Lemma lem7059758 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem7059759 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term171 _126525 x s f) = (term172 _126525 x s f).
Proof. exact (@lem7059757 _126525 x s f (@lem7059758 _126525 s h1)). Qed.
Lemma lem7059769 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term173 A t f t'.
Proof. exact (@lem7059747 A t f h1 t'). Qed.
Lemma lem7059770 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term173 A t f t') = (term119 A t f t').
Proof. exact (eq_refl (term173 A t f t')). Qed.
Lemma lem7059771 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term119 A t f t'.
Proof. exact (EQ_MP (@lem7059770 A t f t') (@lem7059769 A t' t f h1)). Qed.
Lemma lem7059772 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (f : type686 A) (h1 : term115 A t t' f) : term115 A t t' f.
Proof. exact (h1). Qed.
Lemma lem7059773 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : term115 A t t' f) : @FINITE A t'.
Proof. exact (@lem7059771 A t' t f h1 (@lem7059772 A t t' f h2)). Qed.
Lemma lem7059774 {A : Type'} (t' : A -> Prop) : (@FINITE A t') = ((@FINITE A t') = True).
Proof. exact (@lem7 (@FINITE A t')). Qed.
Lemma lem7059775 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : term115 A t t' f) : (@FINITE A t') = True.
Proof. exact (EQ_MP (@lem7059774 A t') (@lem7059773 A t t' f h1 h2)). Qed.
Lemma lem7059781 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term174 A t f t'.
Proof. exact (@lem7059746 A t f h1 t'). Qed.
Lemma lem7059782 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term174 A t f t') = (term139 A t f t').
Proof. exact (eq_refl (term174 A t f t')). Qed.
Lemma lem7059783 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term139 A t f t'.
Proof. exact (EQ_MP (@lem7059782 A t f t') (@lem7059781 A t' t f h1)). Qed.
Lemma lem7059784 {A : Type'} (t' : A -> Prop) (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term175 A t f t' u.
Proof. exact (@lem7059783 A t' t f h1 u). Qed.
Lemma lem7059785 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term175 A t f t' u) = (term135 A t f t' u).
Proof. exact (eq_refl (term175 A t f t' u)). Qed.
Lemma lem7059786 {A : Type'} (t' : A -> Prop) (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term135 A t f t' u.
Proof. exact (EQ_MP (@lem7059785 A t f t' u) (@lem7059784 A t' u t f h1)). Qed.
Lemma lem7059787 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) (h1 : term131 A t f t' u) : term131 A t f t' u.
Proof. exact (h1). Qed.
Lemma lem7059788 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) (h1 : term143 A t f) (h2 : term131 A t f t' u) : (@INTER A t' u) = (@EMPTY A).
Proof. exact (@lem7059786 A t' u t f h1 (@lem7059787 A t f t' u h2)). Qed.
Lemma lem7059797 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term176 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7059798 (p : Prop) (q : Prop) (p' : Prop) : term177 p q p'.
Proof. exact (fun q' : Prop => @lem7059797 p q p' q'). Qed.
Lemma lem7059799 (p : Prop) (q : Prop) : term178 p q.
Proof. exact (fun p' : Prop => @lem7059798 p q p'). Qed.
Lemma lem7059800 {A : Type'} (t : A -> Prop) (f : type686 A) : term179 A t f.
Proof. exact (@lem7059799 (term61 A t f) ((term151 A t f) = (term154 A t f))). Qed.
Lemma lem7059801 {A : Type'} (t : A -> Prop) (f : type686 A) (p' : Prop) : term180 A t f p'.
Proof. exact (@lem7059800 A t f p'). Qed.
Lemma lem7059802 {A : Type'} (t : A -> Prop) (f : type686 A) (p' : Prop) : (term180 A t f p') = (term181 A t f p').
Proof. exact (eq_refl (term180 A t f p')). Qed.
Lemma lem7059803 {A : Type'} (t : A -> Prop) (f : type686 A) (p' : Prop) : term181 A t f p'.
Proof. exact (EQ_MP (@lem7059802 A t f p') (@lem7059801 A t f p')). Qed.
Lemma lem7059804 {A : Type'} (t : A -> Prop) (f : type686 A) (p' : Prop) (q' : Prop) : term182 A t f p' q'.
Proof. exact (@lem7059803 A t f p' q'). Qed.
Lemma lem7059805 {A : Type'} (t : A -> Prop) (f : type686 A) (p' : Prop) (q' : Prop) : (term182 A t f p' q') = (term183 A t f p' q').
Proof. exact (eq_refl (term182 A t f p' q')). Qed.
Lemma lem7059806 {A : Type'} (t : A -> Prop) (f : type686 A) (p' : Prop) (q' : Prop) : term183 A t f p' q'.
Proof. exact (EQ_MP (@lem7059805 A t f p' q') (@lem7059804 A t f p' q')). Qed.
Lemma lem7059812 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term176 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7059813 (p : Prop) (q : Prop) (p' : Prop) : term177 p q p'.
Proof. exact (fun q' : Prop => @lem7059812 p q p' q'). Qed.
Lemma lem7059814 (p : Prop) (q : Prop) : term178 p q.
Proof. exact (fun p' : Prop => @lem7059813 p q p'). Qed.
Lemma lem7059815 {A : Type'} (f : type686 A) : term184 A f.
Proof. exact (@lem7059814 (term42 A f) ((term43 A f) = (@nsum (A -> Prop) f (@CARD A)))). Qed.
Lemma lem7059816 {A : Type'} (f : type686 A) (p' : Prop) : term185 A f p'.
Proof. exact (@lem7059815 A f p'). Qed.
Lemma lem7059817 {A : Type'} (f : type686 A) (p' : Prop) : (term185 A f p') = (term186 A f p').
Proof. exact (eq_refl (term185 A f p')). Qed.
Lemma lem7059818 {A : Type'} (f : type686 A) (p' : Prop) : term186 A f p'.
Proof. exact (EQ_MP (@lem7059817 A f p') (@lem7059816 A f p')). Qed.
Lemma lem7059819 {A : Type'} (f : type686 A) (p' : Prop) (q' : Prop) : term187 A f p' q'.
Proof. exact (@lem7059818 A f p' q'). Qed.
Lemma lem7059820 {A : Type'} (f : type686 A) (p' : Prop) (q' : Prop) : (term187 A f p' q') = (term188 A f p' q').
Proof. exact (eq_refl (term187 A f p' q')). Qed.
Lemma lem7059821 {A : Type'} (f : type686 A) (p' : Prop) (q' : Prop) : term188 A f p' q'.
Proof. exact (EQ_MP (@lem7059820 A f p' q') (@lem7059819 A f p' q')). Qed.
Lemma lem7059879 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term176 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7059880 (p : Prop) (q : Prop) (p' : Prop) : term177 p q p'.
Proof. exact (fun q' : Prop => @lem7059879 p q p' q'). Qed.
Lemma lem7059881 (p : Prop) (q : Prop) : term178 p q.
Proof. exact (fun p' : Prop => @lem7059880 p q p'). Qed.
Lemma lem7059882 {A : Type'} (f : type686 A) (_94244 : A -> Prop) : term189 A f _94244.
Proof. exact (@lem7059881 (@IN (A -> Prop) _94244 f) (@FINITE A _94244)). Qed.
Lemma lem7059883 {A : Type'} (f : type686 A) (_94244 : A -> Prop) (p' : Prop) : term190 A f _94244 p'.
Proof. exact (@lem7059882 A f _94244 p'). Qed.
Lemma lem7059884 {A : Type'} (f : type686 A) (_94244 : A -> Prop) (p' : Prop) : (term190 A f _94244 p') = (term191 A f _94244 p').
Proof. exact (eq_refl (term190 A f _94244 p')). Qed.
Lemma lem7059885 {A : Type'} (f : type686 A) (_94244 : A -> Prop) (p' : Prop) : term191 A f _94244 p'.
Proof. exact (EQ_MP (@lem7059884 A f _94244 p') (@lem7059883 A f _94244 p')). Qed.
Lemma lem7059886 {A : Type'} (f : type686 A) (_94244 : A -> Prop) (p' : Prop) (q' : Prop) : term192 A f _94244 p' q'.
Proof. exact (@lem7059885 A f _94244 p' q'). Qed.
Lemma lem7059887 {A : Type'} (f : type686 A) (_94244 : A -> Prop) (p' : Prop) (q' : Prop) : (term192 A f _94244 p' q') = (term193 A f _94244 p' q').
Proof. exact (eq_refl (term192 A f _94244 p' q')). Qed.
Lemma lem7059888 {A : Type'} (f : type686 A) (_94244 : A -> Prop) (p' : Prop) (q' : Prop) : term193 A f _94244 p' q'.
Proof. exact (EQ_MP (@lem7059887 A f _94244 p' q') (@lem7059886 A f _94244 p' q')). Qed.
Lemma lem7059889 {A : Type'} (_94244 : A -> Prop) (f : type686 A) : (@IN (A -> Prop) _94244 f) = (@IN (A -> Prop) _94244 f).
Proof. exact (eq_refl (@IN (A -> Prop) _94244 f)). Qed.
Lemma lem7059890 {A : Type'} (_94244 : A -> Prop) (f : type686 A) (q' : Prop) : term194 A _94244 f q'.
Proof. exact (@lem7059888 A f _94244 (@IN (A -> Prop) _94244 f) q'). Qed.
Lemma lem7059891 {A : Type'} (_94244 : A -> Prop) (f : type686 A) (q' : Prop) : term195 A _94244 f q'.
Proof. exact (@lem7059890 A _94244 f q' (@lem7059889 A _94244 f)). Qed.
Lemma lem7059892 {A : Type'} (_94244 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94244 f) : @IN (A -> Prop) _94244 f.
Proof. exact (h1). Qed.
Lemma lem7059893 {A : Type'} (_94244 : A -> Prop) (f : type686 A) : (@IN (A -> Prop) _94244 f) = ((@IN (A -> Prop) _94244 f) = True).
Proof. exact (@lem7 (@IN (A -> Prop) _94244 f)). Qed.
Lemma lem7059896 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term196 A t f t'.
Proof. exact (fun h0 : term115 A t t' f => @lem7059775 A t t' f h1 h0). Qed.
Lemma lem7059897 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term196 A t f t'.
Proof. exact (@lem7059896 A t' t f h1). Qed.
Lemma lem7059898 {A : Type'} (_94244 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term196 A t f _94244.
Proof. exact (@lem7059897 A _94244 t f h1). Qed.
Lemma lem7059904 {A : Type'} (_94244 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94244 f) : (@IN (A -> Prop) _94244 f) = True.
Proof. exact (EQ_MP (@lem7059893 A _94244 f) (@lem7059892 A _94244 f h1)). Qed.
Lemma lem7059905 {A : Type'} (_94244 : A -> Prop) (t : A -> Prop) : (term197 A _94244 t) = (term197 A _94244 t).
Proof. exact (eq_refl (term197 A _94244 t)). Qed.
Lemma lem7059906 {A : Type'} (t : A -> Prop) (_94244 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94244 f) : (term115 A t _94244 f) = (term198 A _94244 t).
Proof. exact (MK_COMB (@lem7059905 A _94244 t) (@lem7059904 A _94244 f h1)). Qed.
Lemma lem7059908 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7059909 {A : Type'} (_94244 : A -> Prop) (t : A -> Prop) : (term198 A _94244 t) = True.
Proof. exact (@lem7059908 (_94244 = t)). Qed.
Lemma lem7059910 {A : Type'} (t : A -> Prop) (_94244 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94244 f) : (term115 A t _94244 f) = True.
Proof. exact (TRANS (@lem7059906 A t _94244 f h1) (@lem7059909 A _94244 t)). Qed.
Lemma lem7059911 {A : Type'} (t : A -> Prop) (_94244 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94244 f) : True = (term115 A t _94244 f).
Proof. exact (SYM (@lem7059910 A t _94244 f h1)). Qed.
Lemma lem7059912 {A : Type'} (t : A -> Prop) (_94244 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94244 f) : term115 A t _94244 f.
Proof. exact (EQ_MP (@lem7059911 A t _94244 f h1) (@lem0)). Qed.
Lemma lem7059913 {A : Type'} (t : A -> Prop) (_94244 : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @IN (A -> Prop) _94244 f) : (@FINITE A _94244) = True.
Proof. exact (@lem7059898 A _94244 t f h1 (@lem7059912 A t _94244 f h2)). Qed.
Lemma lem7059914 {A : Type'} (_94244 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term199 A f _94244.
Proof. exact (fun h0 : @IN (A -> Prop) _94244 f => @lem7059913 A t _94244 f h1 h0). Qed.
Lemma lem7059915 {A : Type'} (_94244 : A -> Prop) (f : type686 A) : term200 A _94244 f.
Proof. exact (@lem7059891 A _94244 f True). Qed.
Lemma lem7059916 {A : Type'} (_94244 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term201 A f _94244) = (term202 A _94244 f).
Proof. exact (@lem7059915 A _94244 f (@lem7059914 A _94244 t f h1)). Qed.
Lemma lem7059918 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7059919 {A : Type'} (_94244 : A -> Prop) (f : type686 A) : (term202 A _94244 f) = True.
Proof. exact (@lem7059918 (@IN (A -> Prop) _94244 f)). Qed.
Lemma lem7059920 {A : Type'} (_94244 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term201 A f _94244) = True.
Proof. exact (TRANS (@lem7059916 A _94244 t f h1) (@lem7059919 A _94244 f)). Qed.
Lemma lem7059923 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term203 A f) = (term89 A).
Proof. exact (fun_ext (fun _94244 : A -> Prop => @lem7059920 A _94244 t f h1)). Qed.
Lemma lem7059924 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7059925 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term204 A f) = (term91 A).
Proof. exact (MK_COMB (@lem7059924 A) (@lem7059923 A t f h1)). Qed.
Lemma lem7059927 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7059928 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (@lem7059927 (A -> Prop) t). Qed.
Lemma lem7059929 {A : Type'} : (term91 A) = True.
Proof. exact (@lem7059928 A True). Qed.
Lemma lem7059930 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term204 A f) = True.
Proof. exact (TRANS (@lem7059925 A t f h1) (@lem7059929 A)). Qed.
Lemma lem7059931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7059932 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term205 A f) = (and True).
Proof. exact (MK_COMB (@lem7059931) (@lem7059930 A t f h1)). Qed.
Lemma lem7060078 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term176 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7060079 (p : Prop) (q : Prop) (p' : Prop) : term177 p q p'.
Proof. exact (fun q' : Prop => @lem7060078 p q p' q'). Qed.
Lemma lem7060080 (p : Prop) (q : Prop) : term178 p q.
Proof. exact (fun p' : Prop => @lem7060079 p q p'). Qed.
Lemma lem7060081 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) : term206 A f _94245 u.
Proof. exact (@lem7060080 (term207 A f _94245 u) ((@INTER A _94245 u) = (@EMPTY A))). Qed.
Lemma lem7060082 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (p' : Prop) : term208 A f _94245 u p'.
Proof. exact (@lem7060081 A f _94245 u p'). Qed.
Lemma lem7060083 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (p' : Prop) : (term208 A f _94245 u p') = (term209 A f _94245 u p').
Proof. exact (eq_refl (term208 A f _94245 u p')). Qed.
Lemma lem7060084 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (p' : Prop) : term209 A f _94245 u p'.
Proof. exact (EQ_MP (@lem7060083 A f _94245 u p') (@lem7060082 A f _94245 u p')). Qed.
Lemma lem7060085 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (p' : Prop) (q' : Prop) : term210 A f _94245 u p' q'.
Proof. exact (@lem7060084 A f _94245 u p' q'). Qed.
Lemma lem7060086 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (p' : Prop) (q' : Prop) : (term210 A f _94245 u p' q') = (term211 A f _94245 u p' q').
Proof. exact (eq_refl (term210 A f _94245 u p' q')). Qed.
Lemma lem7060087 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (p' : Prop) (q' : Prop) : term211 A f _94245 u p' q'.
Proof. exact (EQ_MP (@lem7060086 A f _94245 u p' q') (@lem7060085 A f _94245 u p' q')). Qed.
Lemma lem7060094 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) : (term207 A f _94245 u) = (term207 A f _94245 u).
Proof. exact (eq_refl (term207 A f _94245 u)). Qed.
Lemma lem7060095 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (q' : Prop) : term212 A f _94245 u q'.
Proof. exact (@lem7060087 A f _94245 u (term207 A f _94245 u) q'). Qed.
Lemma lem7060096 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (q' : Prop) : term213 A f _94245 u q'.
Proof. exact (@lem7060095 A f _94245 u q' (@lem7060094 A f _94245 u)). Qed.
Lemma lem7060097 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : term207 A f _94245 u.
Proof. exact (h1). Qed.
Lemma lem7060098 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : term214 A f _94245 u.
Proof. exact (proj2 (@lem7060097 A f _94245 u h1)). Qed.
Lemma lem7060099 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : term96 A _94245 u.
Proof. exact (proj2 (@lem7060098 A f _94245 u h1)). Qed.
Lemma lem7060100 {A : Type'} (_94245 : A -> Prop) (u : A -> Prop) : term215 A _94245 u.
Proof. exact (@lem82 (_94245 = u)). Qed.
Lemma lem7060113 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : @IN (A -> Prop) u f.
Proof. exact (proj1 (@lem7060098 A f _94245 u h1)). Qed.
Lemma lem7060114 {A : Type'} (u : A -> Prop) (f : type686 A) : (@IN (A -> Prop) u f) = ((@IN (A -> Prop) u f) = True).
Proof. exact (@lem7 (@IN (A -> Prop) u f)). Qed.
Lemma lem7060116 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : @IN (A -> Prop) _94245 f.
Proof. exact (proj1 (@lem7060097 A f _94245 u h1)). Qed.
Lemma lem7060117 {A : Type'} (_94245 : A -> Prop) (f : type686 A) : (@IN (A -> Prop) _94245 f) = ((@IN (A -> Prop) _94245 f) = True).
Proof. exact (@lem7 (@IN (A -> Prop) _94245 f)). Qed.
Lemma lem7060122 {A : Type'} (t' : A -> Prop) (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term135 A t f t' u.
Proof. exact (fun h0 : term131 A t f t' u => @lem7059788 A t f t' u h1 h0). Qed.
Lemma lem7060123 {A : Type'} (t' : A -> Prop) (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term135 A t f t' u.
Proof. exact (@lem7060122 A t' u t f h1). Qed.
Lemma lem7060124 {A : Type'} (_94245 : A -> Prop) (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term135 A t f _94245 u.
Proof. exact (@lem7060123 A _94245 u t f h1). Qed.
Lemma lem7060132 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (@IN (A -> Prop) _94245 f) = True.
Proof. exact (EQ_MP (@lem7060117 A _94245 f) (@lem7060116 A f _94245 u h1)). Qed.
Lemma lem7060133 {A : Type'} (_94245 : A -> Prop) (t : A -> Prop) : (term197 A _94245 t) = (term197 A _94245 t).
Proof. exact (eq_refl (term197 A _94245 t)). Qed.
Lemma lem7060134 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term115 A t _94245 f) = (term198 A _94245 t).
Proof. exact (MK_COMB (@lem7060133 A _94245 t) (@lem7060132 A f _94245 u h1)). Qed.
Lemma lem7060136 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7060137 {A : Type'} (_94245 : A -> Prop) (t : A -> Prop) : (term198 A _94245 t) = True.
Proof. exact (@lem7060136 (_94245 = t)). Qed.
Lemma lem7060138 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term115 A t _94245 f) = True.
Proof. exact (TRANS (@lem7060134 A t f _94245 u h1) (@lem7060137 A _94245 t)). Qed.
Lemma lem7060139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7060140 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term127 A t _94245 f) = (and True).
Proof. exact (MK_COMB (@lem7060139) (@lem7060138 A t f _94245 u h1)). Qed.
Lemma lem7060148 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (@IN (A -> Prop) u f) = True.
Proof. exact (EQ_MP (@lem7060114 A u f) (@lem7060113 A f _94245 u h1)). Qed.
Lemma lem7060149 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term197 A u t) = (term197 A u t).
Proof. exact (eq_refl (term197 A u t)). Qed.
Lemma lem7060150 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term115 A t u f) = (term198 A u t).
Proof. exact (MK_COMB (@lem7060149 A u t) (@lem7060148 A f _94245 u h1)). Qed.
Lemma lem7060152 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7060153 {A : Type'} (u : A -> Prop) (t : A -> Prop) : (term198 A u t) = True.
Proof. exact (@lem7060152 (u = t)). Qed.
Lemma lem7060154 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term115 A t u f) = True.
Proof. exact (TRANS (@lem7060150 A t f _94245 u h1) (@lem7060153 A u t)). Qed.
Lemma lem7060155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7060156 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term127 A t u f) = (and True).
Proof. exact (MK_COMB (@lem7060155) (@lem7060154 A t f _94245 u h1)). Qed.
Lemma lem7060158 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (_94245 = u) = False.
Proof. exact (@lem7060100 A _94245 u (@lem7060099 A f _94245 u h1)). Qed.
Lemma lem7060159 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7060160 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term96 A _94245 u) = (~ False).
Proof. exact (MK_COMB (@lem7060159) (@lem7060158 A f _94245 u h1)). Qed.
Lemma lem7060162 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7060163 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term96 A _94245 u) = True.
Proof. exact (TRANS (@lem7060160 A f _94245 u h1) (@lem7060162)). Qed.
Lemma lem7060164 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term129 A t f _94245 u) = (True /\ True).
Proof. exact (MK_COMB (@lem7060156 A t f _94245 u h1) (@lem7060163 A f _94245 u h1)). Qed.
Lemma lem7060166 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7060167 : (True /\ True) = True.
Proof. exact (@lem7060166 True). Qed.
Lemma lem7060168 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term129 A t f _94245 u) = True.
Proof. exact (TRANS (@lem7060164 A t f _94245 u h1) (@lem7060167)). Qed.
Lemma lem7060169 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term131 A t f _94245 u) = (True /\ True).
Proof. exact (MK_COMB (@lem7060140 A t f _94245 u h1) (@lem7060168 A t f _94245 u h1)). Qed.
Lemma lem7060171 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7060172 : (True /\ True) = True.
Proof. exact (@lem7060171 True). Qed.
Lemma lem7060173 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : (term131 A t f _94245 u) = True.
Proof. exact (TRANS (@lem7060169 A t f _94245 u h1) (@lem7060172)). Qed.
Lemma lem7060174 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : True = (term131 A t f _94245 u).
Proof. exact (SYM (@lem7060173 A t f _94245 u h1)). Qed.
Lemma lem7060175 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term207 A f _94245 u) : term131 A t f _94245 u.
Proof. exact (EQ_MP (@lem7060174 A t f _94245 u h1) (@lem0)). Qed.
Lemma lem7060176 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term143 A t f) (h2 : term207 A f _94245 u) : (@INTER A _94245 u) = (@EMPTY A).
Proof. exact (@lem7060124 A _94245 u t f h1 (@lem7060175 A t f _94245 u h2)). Qed.
Lemma lem7060177 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem7060178 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term143 A t f) (h2 : term207 A f _94245 u) : (term216 A _94245 u) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem7060177 A) (@lem7060176 A t f _94245 u h1 h2)). Qed.
Lemma lem7060179 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem7060180 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term143 A t f) (h2 : term207 A f _94245 u) : ((@INTER A _94245 u) = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem7060178 A t f _94245 u h1 h2) (@lem7060179 A)). Qed.
Lemma lem7060182 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7060183 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem7060182 (A -> Prop) x). Qed.
Lemma lem7060184 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem7060183 A (@EMPTY A)). Qed.
Lemma lem7060185 {A : Type'} (t : A -> Prop) (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) (h1 : term143 A t f) (h2 : term207 A f _94245 u) : ((@INTER A _94245 u) = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem7060180 A t f _94245 u h1 h2) (@lem7060184 A)). Qed.
Lemma lem7060186 {A : Type'} (_94245 : A -> Prop) (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term217 A f _94245 u.
Proof. exact (fun h0 : term207 A f _94245 u => @lem7060185 A t f _94245 u h1 h0). Qed.
Lemma lem7060187 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) : term218 A f _94245 u.
Proof. exact (@lem7060096 A f _94245 u True). Qed.
Lemma lem7060188 {A : Type'} (_94245 : A -> Prop) (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : (term219 A f _94245 u) = (term220 A f _94245 u).
Proof. exact (@lem7060187 A f _94245 u (@lem7060186 A _94245 u t f h1)). Qed.
Lemma lem7060190 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7060191 {A : Type'} (f : type686 A) (_94245 : A -> Prop) (u : A -> Prop) : (term220 A f _94245 u) = True.
Proof. exact (@lem7060190 (term207 A f _94245 u)). Qed.
Lemma lem7060192 {A : Type'} (_94245 : A -> Prop) (u : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : (term219 A f _94245 u) = True.
Proof. exact (TRANS (@lem7060188 A _94245 u t f h1) (@lem7060191 A f _94245 u)). Qed.
Lemma lem7060193 {A : Type'} (_94245 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : (term221 A f _94245) = (term89 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7060192 A _94245 u t f h1)). Qed.
Lemma lem7060194 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7060195 {A : Type'} (_94245 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : (term222 A f _94245) = (term91 A).
Proof. exact (MK_COMB (@lem7060194 A) (@lem7060193 A _94245 t f h1)). Qed.
Lemma lem7060197 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7060198 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (@lem7060197 (A -> Prop) t). Qed.
Lemma lem7060199 {A : Type'} : (term91 A) = True.
Proof. exact (@lem7060198 A True). Qed.
Lemma lem7060200 {A : Type'} (_94245 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : (term222 A f _94245) = True.
Proof. exact (TRANS (@lem7060195 A _94245 t f h1) (@lem7060199 A)). Qed.
Lemma lem7060203 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : (term223 A f) = (term89 A).
Proof. exact (fun_ext (fun _94245 : A -> Prop => @lem7060200 A _94245 t f h1)). Qed.
Lemma lem7060204 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7060205 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : (term224 A f) = (term91 A).
Proof. exact (MK_COMB (@lem7060204 A) (@lem7060203 A t f h1)). Qed.
Lemma lem7060207 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7060208 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (@lem7060207 (A -> Prop) t). Qed.
Lemma lem7060209 {A : Type'} : (term91 A) = True.
Proof. exact (@lem7060208 A True). Qed.
Lemma lem7060210 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : (term224 A f) = True.
Proof. exact (TRANS (@lem7060205 A t f h1) (@lem7060209 A)). Qed.
Lemma lem7060211 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : (term42 A f) = (True /\ True).
Proof. exact (MK_COMB (@lem7059932 A t f h2) (@lem7060210 A t f h1)). Qed.
Lemma lem7060213 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7060214 : (True /\ True) = True.
Proof. exact (@lem7060213 True). Qed.
Lemma lem7060215 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : (term42 A f) = True.
Proof. exact (TRANS (@lem7060211 A t f h1 h2) (@lem7060214)). Qed.
Lemma lem7060216 {A : Type'} (f : type686 A) (q' : Prop) : term225 A f q'.
Proof. exact (@lem7059821 A f True q'). Qed.
Lemma lem7060217 {A : Type'} (q' : Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : term226 A f q'.
Proof. exact (@lem7060216 A f q' (@lem7060215 A t f h1 h2)). Qed.
Lemma lem7060225 {A : Type'} (f : type686 A) : ((term43 A f) = (@nsum (A -> Prop) f (@CARD A))) = ((term43 A f) = (@nsum (A -> Prop) f (@CARD A))).
Proof. exact (eq_refl ((term43 A f) = (@nsum (A -> Prop) f (@CARD A)))). Qed.
Lemma lem7060226 {A : Type'} (f : type686 A) : term227 A f.
Proof. exact (fun h0 : True => @lem7060225 A f). Qed.
Lemma lem7060227 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : term228 A f.
Proof. exact (@lem7060217 A ((term43 A f) = (@nsum (A -> Prop) f (@CARD A))) t f h1 h2). Qed.
Lemma lem7060228 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : (term56 A f) = (term229 A f).
Proof. exact (@lem7060227 A t f h1 h2 (@lem7060226 A f)). Qed.
Lemma lem7060230 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7060231 {A : Type'} (f : type686 A) : (term229 A f) = ((term43 A f) = (@nsum (A -> Prop) f (@CARD A))).
Proof. exact (@lem7060230 ((term43 A f) = (@nsum (A -> Prop) f (@CARD A)))). Qed.
Lemma lem7060234 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : (term56 A f) = ((term43 A f) = (@nsum (A -> Prop) f (@CARD A))).
Proof. exact (TRANS (@lem7060228 A t f h1 h2) (@lem7060231 A f)). Qed.
Lemma lem7060235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7060236 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : (term58 A f) = (term230 A f).
Proof. exact (MK_COMB (@lem7060235) (@lem7060234 A t f h1 h2)). Qed.
Lemma lem7060245 {A : Type'} (t : A -> Prop) (f : type686 A) : (term59 A t f) = (term59 A t f).
Proof. exact (eq_refl (term59 A t f)). Qed.
Lemma lem7060246 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : (term61 A t f) = (term231 A t f).
Proof. exact (MK_COMB (@lem7060236 A t f h1 h2) (@lem7060245 A t f)). Qed.
Lemma lem7060257 {A : Type'} (t : A -> Prop) (f : type686 A) (q' : Prop) : term232 A t f q'.
Proof. exact (@lem7059806 A t f (term231 A t f) q'). Qed.
Lemma lem7060258 {A : Type'} (q' : Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : term233 A t f q'.
Proof. exact (@lem7060257 A t f q' (@lem7060246 A t f h1 h2)). Qed.
Lemma lem7060259 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : term231 A t f.
Proof. exact (h1). Qed.
Lemma lem7060260 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : term59 A t f.
Proof. exact (proj2 (@lem7060259 A t f h1)). Qed.
Lemma lem7060261 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : @FINITE (A -> Prop) f.
Proof. exact (proj2 (@lem7060260 A t f h1)). Qed.
Lemma lem7060262 {A : Type'} (f : type686 A) : (@FINITE (A -> Prop) f) = ((@FINITE (A -> Prop) f) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) f)). Qed.
Lemma lem7060264 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : term234 A t f.
Proof. exact (proj1 (@lem7060260 A t f h1)). Qed.
Lemma lem7060265 {A : Type'} (t : A -> Prop) (f : type686 A) : term235 A t f.
Proof. exact (@lem82 (@IN (A -> Prop) t f)). Qed.
Lemma lem7060271 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term170 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem7059759 _126525 x f s h0). Qed.
Lemma lem7060272 {A : Type'} (x : A -> Prop) (s : type686 A) (f : type687 A) : term236 A x s f.
Proof. exact (@lem7060271 (A -> Prop) x s f). Qed.
Lemma lem7060273 {A : Type'} (t : A -> Prop) (f : type686 A) : term237 A t f.
Proof. exact (@lem7060272 A t f (@CARD A)). Qed.
Lemma lem7060275 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : (@FINITE (A -> Prop) f) = True.
Proof. exact (EQ_MP (@lem7060262 A f) (@lem7060261 A t f h1)). Qed.
Lemma lem7060276 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : True = (@FINITE (A -> Prop) f).
Proof. exact (SYM (@lem7060275 A t f h1)). Qed.
Lemma lem7060277 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : @FINITE (A -> Prop) f.
Proof. exact (EQ_MP (@lem7060276 A t f h1) (@lem0)). Qed.
Lemma lem7060278 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : (term154 A t f) = (term238 A t f).
Proof. exact (@lem7060273 A t f (@lem7060277 A t f h1)). Qed.
Lemma lem7060280 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term239 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7060281 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term240 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7060280 _2963 g t e g' t' e'). Qed.
Lemma lem7060282 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term241 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7060281 _2963 g t e g' t'). Qed.
Lemma lem7060283 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term242 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7060282 _2963 g t e g'). Qed.
Lemma lem7060284 (g : Prop) (t : nat) (e : nat) : term243 g t e.
Proof. exact (@lem7060283 nat g t e). Qed.
Lemma lem7060285 {A : Type'} (t : A -> Prop) (f : type686 A) : term244 A t f.
Proof. exact (@lem7060284 (@IN (A -> Prop) t f) (@nsum (A -> Prop) f (@CARD A)) (term245 A t f)). Qed.
Lemma lem7060286 {A : Type'} (t : A -> Prop) (f : type686 A) (g' : Prop) : term246 A t f g'.
Proof. exact (@lem7060285 A t f g'). Qed.
Lemma lem7060287 {A : Type'} (t : A -> Prop) (f : type686 A) (g' : Prop) : (term246 A t f g') = (term247 A t f g').
Proof. exact (eq_refl (term246 A t f g')). Qed.
Lemma lem7060288 {A : Type'} (t : A -> Prop) (f : type686 A) (g' : Prop) : term247 A t f g'.
Proof. exact (EQ_MP (@lem7060287 A t f g') (@lem7060286 A t f g')). Qed.
Lemma lem7060289 {A : Type'} (t : A -> Prop) (f : type686 A) (g' : Prop) (t' : nat) : term248 A t f g' t'.
Proof. exact (@lem7060288 A t f g' t'). Qed.
Lemma lem7060290 {A : Type'} (t : A -> Prop) (f : type686 A) (g' : Prop) (t' : nat) : (term248 A t f g' t') = (term249 A t f g' t').
Proof. exact (eq_refl (term248 A t f g' t')). Qed.
Lemma lem7060291 {A : Type'} (t : A -> Prop) (f : type686 A) (g' : Prop) (t' : nat) : term249 A t f g' t'.
Proof. exact (EQ_MP (@lem7060290 A t f g' t') (@lem7060289 A t f g' t')). Qed.
Lemma lem7060292 {A : Type'} (t : A -> Prop) (f : type686 A) (g' : Prop) (t' : nat) (e' : nat) : term250 A t f g' t' e'.
Proof. exact (@lem7060291 A t f g' t' e'). Qed.
Lemma lem7060293 {A : Type'} (t : A -> Prop) (f : type686 A) (g' : Prop) (t' : nat) (e' : nat) : (term250 A t f g' t' e') = (term251 A t f g' t' e').
Proof. exact (eq_refl (term250 A t f g' t' e')). Qed.
Lemma lem7060294 {A : Type'} (t : A -> Prop) (f : type686 A) (g' : Prop) (t' : nat) (e' : nat) : term251 A t f g' t' e'.
Proof. exact (EQ_MP (@lem7060293 A t f g' t' e') (@lem7060292 A t f g' t' e')). Qed.
Lemma lem7060296 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : (@IN (A -> Prop) t f) = False.
Proof. exact (@lem7060265 A t f (@lem7060264 A t f h1)). Qed.
Lemma lem7060297 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : nat) (e' : nat) : term252 A t f t' e'.
Proof. exact (@lem7060294 A t f False t' e'). Qed.
Lemma lem7060298 {A : Type'} (t' : nat) (e' : nat) (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : term253 A t f t' e'.
Proof. exact (@lem7060297 A t f t' e' (@lem7060296 A t f h1)). Qed.
Lemma lem7060302 {A : Type'} (f : type686 A) : (@nsum (A -> Prop) f (@CARD A)) = (@nsum (A -> Prop) f (@CARD A)).
Proof. exact (eq_refl (@nsum (A -> Prop) f (@CARD A))). Qed.
Lemma lem7060303 {A : Type'} (f : type686 A) : term254 A f.
Proof. exact (fun h0 : False => @lem7060302 A f). Qed.
Lemma lem7060304 {A : Type'} (e' : nat) (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : term255 A t f e'.
Proof. exact (@lem7060298 A (@nsum (A -> Prop) f (@CARD A)) e' t f h1). Qed.
Lemma lem7060305 {A : Type'} (e' : nat) (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : term256 A t f e'.
Proof. exact (@lem7060304 A e' t f h1 (@lem7060303 A f)). Qed.
Lemma lem7060311 {A : Type'} (t : A -> Prop) (f : type686 A) : (term245 A t f) = (term245 A t f).
Proof. exact (eq_refl (term245 A t f)). Qed.
Lemma lem7060312 {A : Type'} (t : A -> Prop) (f : type686 A) : term257 A t f.
Proof. exact (fun h0 : ~ False => @lem7060311 A t f). Qed.
Lemma lem7060313 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : term258 A t f.
Proof. exact (@lem7060305 A (term245 A t f) t f h1). Qed.
Lemma lem7060314 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : (term238 A t f) = (term259 A t f).
Proof. exact (@lem7060313 A t f h1 (@lem7060312 A t f)). Qed.
Lemma lem7060316 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7060317 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7060316 nat t1 t2). Qed.
Lemma lem7060318 {A : Type'} (t : A -> Prop) (f : type686 A) : (term259 A t f) = (term245 A t f).
Proof. exact (@lem7060317 (@nsum (A -> Prop) f (@CARD A)) (term245 A t f)). Qed.
Lemma lem7060319 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : (term238 A t f) = (term245 A t f).
Proof. exact (TRANS (@lem7060314 A t f h1) (@lem7060318 A t f)). Qed.
Lemma lem7060320 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : (term154 A t f) = (term245 A t f).
Proof. exact (TRANS (@lem7060278 A t f h1) (@lem7060319 A t f h1)). Qed.
Lemma lem7060321 {A : Type'} (t : A -> Prop) (f : type686 A) : (term153 A t f) = (term153 A t f).
Proof. exact (eq_refl (term153 A t f)). Qed.
Lemma lem7060322 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : ((term151 A t f) = (term154 A t f)) = ((term151 A t f) = (term245 A t f)).
Proof. exact (MK_COMB (@lem7060321 A t f) (@lem7060320 A t f h1)). Qed.
Lemma lem7060325 {A : Type'} (t : A -> Prop) (f : type686 A) : term260 A t f.
Proof. exact (fun h0 : term231 A t f => @lem7060322 A t f h0). Qed.
Lemma lem7060326 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : term261 A t f.
Proof. exact (@lem7060258 A ((term151 A t f) = (term245 A t f)) t f h1 h2). Qed.
Lemma lem7060327 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : (term262 A t f) = (term263 A t f).
Proof. exact (@lem7060326 A t f h1 h2 (@lem7060325 A t f)). Qed.
Lemma lem7060381 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : (term263 A t f) = (term262 A t f).
Proof. exact (SYM (@lem7060327 A t f h1 h2)). Qed.
Lemma lem7060382 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : term231 A t f.
Proof. exact (h1). Qed.
Lemma lem7060383 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term59 A t f) : term59 A t f.
Proof. exact (h1). Qed.
Lemma lem7060384 {A : Type'} (f : type686 A) (h1 : (term43 A f) = (@nsum (A -> Prop) f (@CARD A))) : (term43 A f) = (@nsum (A -> Prop) f (@CARD A)).
Proof. exact (h1). Qed.
Lemma lem7060385 {A : Type'} (f : type686 A) (h1 : (term43 A f) = (@nsum (A -> Prop) f (@CARD A))) : (@nsum (A -> Prop) f (@CARD A)) = (term43 A f).
Proof. exact (SYM (@lem7060384 A f h1)). Qed.
Lemma lem7060386 {A : Type'} (f : type686 A) (t : A -> Prop) : (term264 A f t) = (term264 A f t).
Proof. exact (eq_refl (term264 A f t)). Qed.
Lemma lem7060387 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : (term43 A f) = (@nsum (A -> Prop) f (@CARD A))) : (term265 A t f) = (term266 A t f).
Proof. exact (MK_COMB (@lem7060386 A f t) (@lem7060385 A f h1)). Qed.
Lemma lem7060388 {A : Type'} (t : A -> Prop) (f : type686 A) : (term266 A t f) = ((term151 A t f) = (term267 A t f)).
Proof. exact (eq_refl (term266 A t f)). Qed.
Lemma lem7060389 {A : Type'} (t : A -> Prop) (f : type686 A) : (term268 A t f) = (term268 A t f).
Proof. exact (eq_refl (term268 A t f)). Qed.
Lemma lem7060390 {A : Type'} (t : A -> Prop) (f : type686 A) : ((term265 A t f) = (term266 A t f)) = ((term265 A t f) = ((term151 A t f) = (term267 A t f))).
Proof. exact (MK_COMB (@lem7060389 A t f) (@lem7060388 A t f)). Qed.
Lemma lem7060391 {A : Type'} (t : A -> Prop) (f : type686 A) : (term265 A t f) = ((term151 A t f) = (term245 A t f)).
Proof. exact (eq_refl (term265 A t f)). Qed.
Lemma lem7060392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7060393 {A : Type'} (t : A -> Prop) (f : type686 A) : (term268 A t f) = (term269 A t f).
Proof. exact (MK_COMB (@lem7060392) (@lem7060391 A t f)). Qed.
Lemma lem7060394 {A : Type'} (t : A -> Prop) (f : type686 A) : ((term151 A t f) = (term267 A t f)) = ((term151 A t f) = (term267 A t f)).
Proof. exact (eq_refl ((term151 A t f) = (term267 A t f))). Qed.
Lemma lem7060395 {A : Type'} (t : A -> Prop) (f : type686 A) : ((term265 A t f) = ((term151 A t f) = (term267 A t f))) = (((term151 A t f) = (term245 A t f)) = ((term151 A t f) = (term267 A t f))).
Proof. exact (MK_COMB (@lem7060393 A t f) (@lem7060394 A t f)). Qed.
Lemma lem7060396 {A : Type'} (t : A -> Prop) (f : type686 A) : ((term265 A t f) = (term266 A t f)) = (((term151 A t f) = (term245 A t f)) = ((term151 A t f) = (term267 A t f))).
Proof. exact (TRANS (@lem7060390 A t f) (@lem7060395 A t f)). Qed.
Lemma lem7060397 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : (term43 A f) = (@nsum (A -> Prop) f (@CARD A))) : ((term151 A t f) = (term245 A t f)) = ((term151 A t f) = (term267 A t f)).
Proof. exact (EQ_MP (@lem7060396 A t f) (@lem7060387 A t f h1)). Qed.
Lemma lem7060398 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : (term43 A f) = (@nsum (A -> Prop) f (@CARD A))) : ((term151 A t f) = (term267 A t f)) = ((term151 A t f) = (term245 A t f)).
Proof. exact (SYM (@lem7060397 A t f h1)). Qed.
Lemma lem7060399 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : @FINITE (A -> Prop) f.
Proof. exact (h1). Qed.
Lemma lem7060400 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : term234 A t f.
Proof. exact (h1). Qed.
Lemma lem7060401 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : (term151 A t f) = (term267 A t f)) : (term151 A t f) = (term267 A t f).
Proof. exact (h1). Qed.
Lemma lem7060402 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : (term151 A t f) = (term267 A t f)) : (term267 A t f) = (term151 A t f).
Proof. exact (SYM (@lem7060401 A t f h1)). Qed.
Lemma lem7060403 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : (term267 A t f) = (term151 A t f)) : (term267 A t f) = (term151 A t f).
Proof. exact (h1). Qed.
Lemma lem7060404 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : (term267 A t f) = (term151 A t f)) : (term151 A t f) = (term267 A t f).
Proof. exact (SYM (@lem7060403 A t f h1)). Qed.
Lemma lem7060405 {A : Type'} (t : A -> Prop) (f : type686 A) : ((term151 A t f) = (term267 A t f)) = ((term267 A t f) = (term151 A t f)).
Proof. exact (prop_ext (fun h1 : (term151 A t f) = (term267 A t f) => @lem7060402 A t f h1) (fun h1 : (term267 A t f) = (term151 A t f) => @lem7060404 A t f h1)). Qed.
Lemma lem7060406 {A : Type'} (t : A -> Prop) (f : type686 A) : ((term267 A t f) = (term151 A t f)) = ((term151 A t f) = (term267 A t f)).
Proof. exact (SYM (@lem7060405 A t f)). Qed.
Lemma lem7060408 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : term14 _99816 s t u.
Proof. exact (EQ_MP (@lem7059129 _99816 s t u) (@lem7059128 _99816 s t u)). Qed.
Lemma lem7060409 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term14 A s t u.
Proof. exact (@lem7060408 A s t u). Qed.
Lemma lem7060410 {A : Type'} (t : A -> Prop) (f : type686 A) : term270 A t f.
Proof. exact (@lem7060409 A t (@UNIONS A f) (term149 A t f)). Qed.
Lemma lem7060411 {_87026 : Type'} : term271 _87026.
Proof. exact (proj2 (@lem3341279 Prop _87026)). Qed.
Lemma lem7060412 {_87026 : Type'} (s : type686 _87026) : term272 _87026 s.
Proof. exact (@lem7060411 _87026 s). Qed.
Lemma lem7060413 {_87026 : Type'} (s : type686 _87026) : (term272 _87026 s) = (term273 _87026 s).
Proof. exact (eq_refl (term272 _87026 s)). Qed.
Lemma lem7060414 {_87026 : Type'} (s : type686 _87026) : term273 _87026 s.
Proof. exact (EQ_MP (@lem7060413 _87026 s) (@lem7060412 _87026 s)). Qed.
Lemma lem7060415 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : term274 _87026 s t.
Proof. exact (@lem7060414 _87026 s t). Qed.
Lemma lem7060416 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term274 _87026 s t) = ((term275 _87026 t s) = (term276 _87026 s t)).
Proof. exact (eq_refl (term274 _87026 s t)). Qed.
Lemma lem7060425 {A : Type'} (s : A -> Prop) : term277 A s.
Proof. exact (@lem3606772 A s). Qed.
Lemma lem7060426 {A : Type'} (s : A -> Prop) : (term277 A s) = (term278 A s).
Proof. exact (eq_refl (term277 A s)). Qed.
Lemma lem7060427 {A : Type'} (s : A -> Prop) : term278 A s.
Proof. exact (EQ_MP (@lem7060426 A s) (@lem7060425 A s)). Qed.
Lemma lem7060428 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term279 A s t.
Proof. exact (@lem7060427 A s t). Qed.
Lemma lem7060429 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term279 A s t) = ((term280 A s t) = (term281 A s t)).
Proof. exact (eq_refl (term279 A s t)). Qed.
Lemma lem7060431 {A : Type'} (s : type686 A) : term282 A s.
Proof. exact (@lem4605902 A s). Qed.
Lemma lem7060432 {A : Type'} (s : type686 A) : (term282 A s) = ((term283 A s) = (term284 A s)).
Proof. exact (eq_refl (term282 A s)). Qed.
Lemma lem7060434 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term173 A t f t'.
Proof. exact (@lem7059747 A t f h1 t'). Qed.
Lemma lem7060435 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term173 A t f t') = (term119 A t f t').
Proof. exact (eq_refl (term173 A t f t')). Qed.
Lemma lem7060436 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term119 A t f t'.
Proof. exact (EQ_MP (@lem7060435 A t f t') (@lem7060434 A t' t f h1)). Qed.
Lemma lem7060437 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (f : type686 A) (h1 : term115 A t t' f) : term115 A t t' f.
Proof. exact (h1). Qed.
Lemma lem7060438 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : term115 A t t' f) : @FINITE A t'.
Proof. exact (@lem7060436 A t' t f h1 (@lem7060437 A t t' f h2)). Qed.
Lemma lem7060439 {A : Type'} (t' : A -> Prop) : (@FINITE A t') = ((@FINITE A t') = True).
Proof. exact (@lem7 (@FINITE A t')). Qed.
Lemma lem7060440 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : term115 A t t' f) : (@FINITE A t') = True.
Proof. exact (EQ_MP (@lem7060439 A t') (@lem7060438 A t t' f h1 h2)). Qed.
Lemma lem7060459 {A : Type'} (t : A -> Prop) (f : type686 A) : term235 A t f.
Proof. exact (@lem82 (@IN (A -> Prop) t f)). Qed.
Lemma lem7060461 {A : Type'} (f : type686 A) : (@FINITE (A -> Prop) f) = ((@FINITE (A -> Prop) f) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) f)). Qed.
Lemma lem7060466 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term280 A s t) = (term281 A s t).
Proof. exact (EQ_MP (@lem7060429 A s t) (@lem7060428 A s t)). Qed.
Lemma lem7060467 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term280 A s t) = (term281 A s t).
Proof. exact (@lem7060466 A s t). Qed.
Lemma lem7060468 {A : Type'} (t : A -> Prop) (f : type686 A) : (term285 A t f) = (term286 A t f).
Proof. exact (@lem7060467 A t (@UNIONS A f)). Qed.
Lemma lem7060472 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term196 A t f t'.
Proof. exact (fun h0 : term115 A t t' f => @lem7060440 A t t' f h1 h0). Qed.
Lemma lem7060473 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term196 A t f t'.
Proof. exact (@lem7060472 A t' t f h1). Qed.
Lemma lem7060474 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term287 A f t.
Proof. exact (@lem7060473 A t t f h1). Qed.
Lemma lem7060478 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7060479 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem7060478 (A -> Prop) x). Qed.
Lemma lem7060480 {A : Type'} (t : A -> Prop) : (t = t) = True.
Proof. exact (@lem7060479 A t). Qed.
Lemma lem7060481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7060482 {A : Type'} (t : A -> Prop) : (term288 A t) = (or True).
Proof. exact (MK_COMB (@lem7060481) (@lem7060480 A t)). Qed.
Lemma lem7060484 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : (@IN (A -> Prop) t f) = False.
Proof. exact (@lem7060459 A t f (@lem7060400 A t f h1)). Qed.
Lemma lem7060485 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : (term289 A t f) = (True \/ False).
Proof. exact (MK_COMB (@lem7060482 A t) (@lem7060484 A t f h1)). Qed.
Lemma lem7060487 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7060488 : (True \/ False) = True.
Proof. exact (@lem7060487 False). Qed.
Lemma lem7060489 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : (term289 A t f) = True.
Proof. exact (TRANS (@lem7060485 A t f h1) (@lem7060488)). Qed.
Lemma lem7060490 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : True = (term289 A t f).
Proof. exact (SYM (@lem7060489 A t f h1)). Qed.
Lemma lem7060491 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : term289 A t f.
Proof. exact (EQ_MP (@lem7060490 A t f h1) (@lem0)). Qed.
Lemma lem7060492 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : term234 A t f) : (@FINITE A t) = True.
Proof. exact (@lem7060474 A t f h1 (@lem7060491 A t f h2)). Qed.
Lemma lem7060493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7060494 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : term234 A t f) : (term290 A t) = (and True).
Proof. exact (MK_COMB (@lem7060493) (@lem7060492 A t f h1 h2)). Qed.
Lemma lem7060496 {A : Type'} (s : type686 A) : (term283 A s) = (term284 A s).
Proof. exact (EQ_MP (@lem7060432 A s) (@lem7060431 A s)). Qed.
Lemma lem7060497 {A : Type'} (s : type686 A) : (term283 A s) = (term284 A s).
Proof. exact (@lem7060496 A s). Qed.
Lemma lem7060498 {A : Type'} (f : type686 A) : (term283 A f) = (term284 A f).
Proof. exact (@lem7060497 A f). Qed.
Lemma lem7060502 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (@FINITE (A -> Prop) f) = True.
Proof. exact (EQ_MP (@lem7060461 A f) (@lem7060399 A f h1)). Qed.
Lemma lem7060503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7060504 {A : Type'} (f : type686 A) (h1 : @FINITE (A -> Prop) f) : (term291 A f) = (and True).
Proof. exact (MK_COMB (@lem7060503) (@lem7060502 A f h1)). Qed.
Lemma lem7060564 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term176 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7060565 (p : Prop) (q : Prop) (p' : Prop) : term177 p q p'.
Proof. exact (fun q' : Prop => @lem7060564 p q p' q'). Qed.
Lemma lem7060566 (p : Prop) (q : Prop) : term178 p q.
Proof. exact (fun p' : Prop => @lem7060565 p q p'). Qed.
Lemma lem7060567 {A : Type'} (f : type686 A) (_94248 : A -> Prop) : term189 A f _94248.
Proof. exact (@lem7060566 (@IN (A -> Prop) _94248 f) (@FINITE A _94248)). Qed.
Lemma lem7060568 {A : Type'} (f : type686 A) (_94248 : A -> Prop) (p' : Prop) : term190 A f _94248 p'.
Proof. exact (@lem7060567 A f _94248 p'). Qed.
Lemma lem7060569 {A : Type'} (f : type686 A) (_94248 : A -> Prop) (p' : Prop) : (term190 A f _94248 p') = (term191 A f _94248 p').
Proof. exact (eq_refl (term190 A f _94248 p')). Qed.
Lemma lem7060570 {A : Type'} (f : type686 A) (_94248 : A -> Prop) (p' : Prop) : term191 A f _94248 p'.
Proof. exact (EQ_MP (@lem7060569 A f _94248 p') (@lem7060568 A f _94248 p')). Qed.
Lemma lem7060571 {A : Type'} (f : type686 A) (_94248 : A -> Prop) (p' : Prop) (q' : Prop) : term192 A f _94248 p' q'.
Proof. exact (@lem7060570 A f _94248 p' q'). Qed.
Lemma lem7060572 {A : Type'} (f : type686 A) (_94248 : A -> Prop) (p' : Prop) (q' : Prop) : (term192 A f _94248 p' q') = (term193 A f _94248 p' q').
Proof. exact (eq_refl (term192 A f _94248 p' q')). Qed.
Lemma lem7060573 {A : Type'} (f : type686 A) (_94248 : A -> Prop) (p' : Prop) (q' : Prop) : term193 A f _94248 p' q'.
Proof. exact (EQ_MP (@lem7060572 A f _94248 p' q') (@lem7060571 A f _94248 p' q')). Qed.
Lemma lem7060574 {A : Type'} (_94248 : A -> Prop) (f : type686 A) : (@IN (A -> Prop) _94248 f) = (@IN (A -> Prop) _94248 f).
Proof. exact (eq_refl (@IN (A -> Prop) _94248 f)). Qed.
Lemma lem7060575 {A : Type'} (_94248 : A -> Prop) (f : type686 A) (q' : Prop) : term194 A _94248 f q'.
Proof. exact (@lem7060573 A f _94248 (@IN (A -> Prop) _94248 f) q'). Qed.
Lemma lem7060576 {A : Type'} (_94248 : A -> Prop) (f : type686 A) (q' : Prop) : term195 A _94248 f q'.
Proof. exact (@lem7060575 A _94248 f q' (@lem7060574 A _94248 f)). Qed.
Lemma lem7060577 {A : Type'} (_94248 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94248 f) : @IN (A -> Prop) _94248 f.
Proof. exact (h1). Qed.
Lemma lem7060578 {A : Type'} (_94248 : A -> Prop) (f : type686 A) : (@IN (A -> Prop) _94248 f) = ((@IN (A -> Prop) _94248 f) = True).
Proof. exact (@lem7 (@IN (A -> Prop) _94248 f)). Qed.
Lemma lem7060581 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term196 A t f t'.
Proof. exact (fun h0 : term115 A t t' f => @lem7060440 A t t' f h1 h0). Qed.
Lemma lem7060582 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term196 A t f t'.
Proof. exact (@lem7060581 A t' t f h1). Qed.
Lemma lem7060583 {A : Type'} (_94248 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term196 A t f _94248.
Proof. exact (@lem7060582 A _94248 t f h1). Qed.
Lemma lem7060589 {A : Type'} (_94248 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94248 f) : (@IN (A -> Prop) _94248 f) = True.
Proof. exact (EQ_MP (@lem7060578 A _94248 f) (@lem7060577 A _94248 f h1)). Qed.
Lemma lem7060590 {A : Type'} (_94248 : A -> Prop) (t : A -> Prop) : (term197 A _94248 t) = (term197 A _94248 t).
Proof. exact (eq_refl (term197 A _94248 t)). Qed.
Lemma lem7060591 {A : Type'} (t : A -> Prop) (_94248 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94248 f) : (term115 A t _94248 f) = (term198 A _94248 t).
Proof. exact (MK_COMB (@lem7060590 A _94248 t) (@lem7060589 A _94248 f h1)). Qed.
Lemma lem7060593 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7060594 {A : Type'} (_94248 : A -> Prop) (t : A -> Prop) : (term198 A _94248 t) = True.
Proof. exact (@lem7060593 (_94248 = t)). Qed.
Lemma lem7060595 {A : Type'} (t : A -> Prop) (_94248 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94248 f) : (term115 A t _94248 f) = True.
Proof. exact (TRANS (@lem7060591 A t _94248 f h1) (@lem7060594 A _94248 t)). Qed.
Lemma lem7060596 {A : Type'} (t : A -> Prop) (_94248 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94248 f) : True = (term115 A t _94248 f).
Proof. exact (SYM (@lem7060595 A t _94248 f h1)). Qed.
Lemma lem7060597 {A : Type'} (t : A -> Prop) (_94248 : A -> Prop) (f : type686 A) (h1 : @IN (A -> Prop) _94248 f) : term115 A t _94248 f.
Proof. exact (EQ_MP (@lem7060596 A t _94248 f h1) (@lem0)). Qed.
Lemma lem7060598 {A : Type'} (t : A -> Prop) (_94248 : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @IN (A -> Prop) _94248 f) : (@FINITE A _94248) = True.
Proof. exact (@lem7060583 A _94248 t f h1 (@lem7060597 A t _94248 f h2)). Qed.
Lemma lem7060599 {A : Type'} (_94248 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : term199 A f _94248.
Proof. exact (fun h0 : @IN (A -> Prop) _94248 f => @lem7060598 A t _94248 f h1 h0). Qed.
Lemma lem7060600 {A : Type'} (_94248 : A -> Prop) (f : type686 A) : term200 A _94248 f.
Proof. exact (@lem7060576 A _94248 f True). Qed.
Lemma lem7060601 {A : Type'} (_94248 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term201 A f _94248) = (term202 A _94248 f).
Proof. exact (@lem7060600 A _94248 f (@lem7060599 A _94248 t f h1)). Qed.
Lemma lem7060603 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7060604 {A : Type'} (_94248 : A -> Prop) (f : type686 A) : (term202 A _94248 f) = True.
Proof. exact (@lem7060603 (@IN (A -> Prop) _94248 f)). Qed.
Lemma lem7060605 {A : Type'} (_94248 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term201 A f _94248) = True.
Proof. exact (TRANS (@lem7060601 A _94248 t f h1) (@lem7060604 A _94248 f)). Qed.
Lemma lem7060608 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term203 A f) = (term89 A).
Proof. exact (fun_ext (fun _94248 : A -> Prop => @lem7060605 A _94248 t f h1)). Qed.
Lemma lem7060609 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7060610 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term204 A f) = (term91 A).
Proof. exact (MK_COMB (@lem7060609 A) (@lem7060608 A t f h1)). Qed.
Lemma lem7060612 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7060613 {A : Type'} (t : Prop) : (term93 A t) = t.
Proof. exact (@lem7060612 (A -> Prop) t). Qed.
Lemma lem7060614 {A : Type'} : (term91 A) = True.
Proof. exact (@lem7060613 A True). Qed.
Lemma lem7060615 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) : (term204 A f) = True.
Proof. exact (TRANS (@lem7060610 A t f h1) (@lem7060614 A)). Qed.
Lemma lem7060616 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @FINITE (A -> Prop) f) : (term284 A f) = (True /\ True).
Proof. exact (MK_COMB (@lem7060504 A f h2) (@lem7060615 A t f h1)). Qed.
Lemma lem7060618 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7060619 : (True /\ True) = True.
Proof. exact (@lem7060618 True). Qed.
Lemma lem7060620 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @FINITE (A -> Prop) f) : (term284 A f) = True.
Proof. exact (TRANS (@lem7060616 A t f h1 h2) (@lem7060619)). Qed.
Lemma lem7060621 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @FINITE (A -> Prop) f) : (term283 A f) = True.
Proof. exact (TRANS (@lem7060498 A f) (@lem7060620 A t f h1 h2)). Qed.
Lemma lem7060622 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @FINITE (A -> Prop) f) (h3 : term234 A t f) : (term286 A t f) = (True /\ True).
Proof. exact (MK_COMB (@lem7060494 A t f h1 h3) (@lem7060621 A t f h1 h2)). Qed.
Lemma lem7060624 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7060625 : (True /\ True) = True.
Proof. exact (@lem7060624 True). Qed.
Lemma lem7060626 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @FINITE (A -> Prop) f) (h3 : term234 A t f) : (term286 A t f) = True.
Proof. exact (TRANS (@lem7060622 A t f h1 h2 h3) (@lem7060625)). Qed.
Lemma lem7060627 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @FINITE (A -> Prop) f) (h3 : term234 A t f) : (term285 A t f) = True.
Proof. exact (TRANS (@lem7060468 A t f) (@lem7060626 A t f h1 h2 h3)). Qed.
Lemma lem7060628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7060629 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @FINITE (A -> Prop) f) (h3 : term234 A t f) : (term292 A t f) = (and True).
Proof. exact (MK_COMB (@lem7060628) (@lem7060627 A t f h1 h2 h3)). Qed.
Lemma lem7060635 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term275 _87026 t s) = (term276 _87026 s t).
Proof. exact (EQ_MP (@lem7060416 _87026 s t) (@lem7060415 _87026 s t)). Qed.
Lemma lem7060636 {A : Type'} (s : type686 A) (t : A -> Prop) : (term275 A t s) = (term276 A s t).
Proof. exact (@lem7060635 A s t). Qed.
Lemma lem7060637 {A : Type'} (f : type686 A) (t : A -> Prop) : (term275 A t f) = (term276 A f t).
Proof. exact (@lem7060636 A f t). Qed.
Lemma lem7060688 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem7060689 {A : Type'} (f : type686 A) (t : A -> Prop) : (term293 A t f) = (term294 A f t).
Proof. exact (MK_COMB (@lem7060688 A) (@lem7060637 A f t)). Qed.
Lemma lem7060740 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem7060741 {A : Type'} (f : type686 A) (t : A -> Prop) : ((term275 A t f) = (@EMPTY A)) = ((term276 A f t) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem7060689 A f t) (@lem7060740 A)). Qed.
Lemma lem7060794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7060795 {A : Type'} (f : type686 A) (t : A -> Prop) : (term295 A t f) = (term296 A f t).
Proof. exact (MK_COMB (@lem7060794) (@lem7060741 A f t)). Qed.
Lemma lem7060849 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7060850 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem7060849 (A -> Prop) x). Qed.
Lemma lem7060851 {A : Type'} (t : A -> Prop) (f : type686 A) : ((term149 A t f) = (term149 A t f)) = True.
Proof. exact (@lem7060850 A (term149 A t f)). Qed.
Lemma lem7060852 {A : Type'} (f : type686 A) (t : A -> Prop) : (term297 A t f) = (term298 A f t).
Proof. exact (MK_COMB (@lem7060795 A f t) (@lem7060851 A t f)). Qed.
Lemma lem7060854 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7060855 {A : Type'} (f : type686 A) (t : A -> Prop) : (term298 A f t) = ((term276 A f t) = (@EMPTY A)).
Proof. exact (@lem7060854 ((term276 A f t) = (@EMPTY A))). Qed.
Lemma lem7060908 {A : Type'} (f : type686 A) (t : A -> Prop) : (term297 A t f) = ((term276 A f t) = (@EMPTY A)).
Proof. exact (TRANS (@lem7060852 A f t) (@lem7060855 A f t)). Qed.
Lemma lem7060909 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @FINITE (A -> Prop) f) (h3 : term234 A t f) : (term299 A t f) = (term300 A f t).
Proof. exact (MK_COMB (@lem7060629 A t f h1 h2 h3) (@lem7060908 A f t)). Qed.
Lemma lem7060911 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7060912 {A : Type'} (f : type686 A) (t : A -> Prop) : (term300 A f t) = ((term276 A f t) = (@EMPTY A)).
Proof. exact (@lem7060911 ((term276 A f t) = (@EMPTY A))). Qed.
Lemma lem7060965 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @FINITE (A -> Prop) f) (h3 : term234 A t f) : (term299 A t f) = ((term276 A f t) = (@EMPTY A)).
Proof. exact (TRANS (@lem7060909 A t f h1 h2 h3) (@lem7060912 A f t)). Qed.
Lemma lem7060966 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : @FINITE (A -> Prop) f) (h3 : term234 A t f) : ((term276 A f t) = (@EMPTY A)) = (term299 A t f).
Proof. exact (SYM (@lem7060965 A t f h1 h2 h3)). Qed.
Lemma lem7060968 {_86951 : Type'} (s : type686 _86951) : ((@UNIONS _86951 s) = (@EMPTY _86951)) = (term7 _86951 s).
Proof. exact (EQ_MP (@lem7059099 _86951 s) (@lem7059098 _86951 s)). Qed.
Lemma lem7060969 {A : Type'} (s : type686 A) : ((@UNIONS A s) = (@EMPTY A)) = (term7 A s).
Proof. exact (@lem7060968 A s). Qed.
Lemma lem7060970 {A : Type'} (f : type686 A) (t : A -> Prop) : ((term276 A f t) = (@EMPTY A)) = (term301 A f t).
Proof. exact (@lem7060969 A (term302 A f t)). Qed.
Lemma lem7060980 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term4 _83064 x P) = (term5 _83064 P x).
Proof. exact (EQ_MP (@lem7059096 _83064 P x) (@lem7059095 _83064 P x)). Qed.
Lemma lem7060981 {A : Type'} (P : type909 A) (x : A -> Prop) : (term303 A x P) = (term304 A P x).
Proof. exact (@lem7060980 (A -> Prop) P x). Qed.
Lemma lem7060982 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term305 A t' f t) = (term306 A f t t').
Proof. exact (@lem7060981 A (term307 A f t) t'). Qed.
Lemma lem7060983 {A : Type'} (GEN_PVAR_22 : A -> Prop) (f : type686 A) (t : A -> Prop) : (term308 A f t GEN_PVAR_22) = (term309 A GEN_PVAR_22 f t).
Proof. exact (eq_refl (term308 A f t GEN_PVAR_22)). Qed.
Lemma lem7060984 {A : Type'} (f : type686 A) (t : A -> Prop) : (term310 A f t) = (term311 A f t).
Proof. exact (fun_ext (fun GEN_PVAR_22 : A -> Prop => @lem7060983 A GEN_PVAR_22 f t)). Qed.
Lemma lem7060985 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem7060986 {A : Type'} (f : type686 A) (t : A -> Prop) : (term312 A f t) = (term302 A f t).
Proof. exact (MK_COMB (@lem7060985 A) (@lem7060984 A f t)). Qed.
Lemma lem7060987 {A : Type'} (t' : A -> Prop) : (@IN (A -> Prop) t') = (@IN (A -> Prop) t').
Proof. exact (eq_refl (@IN (A -> Prop) t')). Qed.
Lemma lem7060988 {A : Type'} (t' : A -> Prop) (f : type686 A) (t : A -> Prop) : (term305 A t' f t) = (term313 A t' f t).
Proof. exact (MK_COMB (@lem7060987 A t') (@lem7060986 A f t)). Qed.
Lemma lem7060989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7060990 {A : Type'} (t' : A -> Prop) (f : type686 A) (t : A -> Prop) : (term314 A t' f t) = (term315 A t' f t).
Proof. exact (MK_COMB (@lem7060989) (@lem7060988 A t' f t)). Qed.
Lemma lem7060991 {A : Type'} (t' : A -> Prop) (f : type686 A) (t : A -> Prop) : (term306 A f t t') = (term316 A t' f t).
Proof. exact (eq_refl (term306 A f t t')). Qed.
Lemma lem7060992 {A : Type'} (t' : A -> Prop) (f : type686 A) (t : A -> Prop) : ((term305 A t' f t) = (term306 A f t t')) = ((term313 A t' f t) = (term316 A t' f t)).
Proof. exact (MK_COMB (@lem7060990 A t' f t) (@lem7060991 A t' f t)). Qed.
Lemma lem7060993 {A : Type'} (t' : A -> Prop) (f : type686 A) (t : A -> Prop) : (term313 A t' f t) = (term316 A t' f t).
Proof. exact (EQ_MP (@lem7060992 A t' f t) (@lem7060982 A f t t')). Qed.
Lemma lem7060999 {A B : Type'} (f : A -> B) (y : A) : (term317 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7061000 {A : Type'} (f : type1527 A) (y : Prop) : (term318 A f y) = (f y).
Proof. exact (@lem7060999 Prop (type686 A) f y). Qed.
Lemma lem7061001 {A : Type'} (t' : A -> Prop) (x : A -> Prop) (f : type686 A) : (term319 A t' x f) = (term320 A t' x f).
Proof. exact (@lem7061000 A (term321 A t') (@IN (A -> Prop) x f)). Qed.
Lemma lem7061002 {A : Type'} (p : Prop) (t' : A -> Prop) : (term322 A t' p) = (term323 A p t').
Proof. exact (eq_refl (term322 A t' p)). Qed.
Lemma lem7061003 {A : Type'} (t' : A -> Prop) : (term324 A t') = (term321 A t').
Proof. exact (fun_ext (fun p : Prop => @lem7061002 A p t')). Qed.
Lemma lem7061004 {A : Type'} (x : A -> Prop) (f : type686 A) : (@IN (A -> Prop) x f) = (@IN (A -> Prop) x f).
Proof. exact (eq_refl (@IN (A -> Prop) x f)). Qed.
Lemma lem7061005 {A : Type'} (t' : A -> Prop) (x : A -> Prop) (f : type686 A) : (term319 A t' x f) = (term320 A t' x f).
Proof. exact (MK_COMB (@lem7061003 A t') (@lem7061004 A x f)). Qed.
Lemma lem7061006 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem7061007 {A : Type'} (t' : A -> Prop) (x : A -> Prop) (f : type686 A) : (term325 A t' x f) = (term326 A t' x f).
Proof. exact (MK_COMB (@lem7061006 A) (@lem7061005 A t' x f)). Qed.
Lemma lem7061008 {A : Type'} (x : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term320 A t' x f) = (term327 A x f t').
Proof. exact (eq_refl (term320 A t' x f)). Qed.
Lemma lem7061009 {A : Type'} (x : A -> Prop) (f : type686 A) (t' : A -> Prop) : ((term319 A t' x f) = (term320 A t' x f)) = ((term320 A t' x f) = (term327 A x f t')).
Proof. exact (MK_COMB (@lem7061007 A t' x f) (@lem7061008 A x f t')). Qed.
Lemma lem7061010 {A : Type'} (x : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term320 A t' x f) = (term327 A x f t').
Proof. exact (EQ_MP (@lem7061009 A x f t') (@lem7061001 A t' x f)). Qed.
Lemma lem7061015 {A : Type'} (t : A -> Prop) (x : A -> Prop) : (@INTER A t x) = (@INTER A t x).
Proof. exact (eq_refl (@INTER A t x)). Qed.
Lemma lem7061016 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term328 A t' f t x) = (term329 A f t' t x).
Proof. exact (MK_COMB (@lem7061010 A x f t') (@lem7061015 A t x)). Qed.
Lemma lem7061018 {A B : Type'} (f : A -> B) (y : A) : (term317 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7061019 {A : Type'} (f : type686 A) (y : A -> Prop) : (term330 A f y) = (f y).
Proof. exact (@lem7061018 (A -> Prop) Prop f y). Qed.
Lemma lem7061020 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term331 A f t' t x) = (term329 A f t' t x).
Proof. exact (@lem7061019 A (term327 A x f t') (@INTER A t x)). Qed.
Lemma lem7061021 {A : Type'} (x : A -> Prop) (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term332 A x f t' t) = (term333 A x f t' t).
Proof. exact (eq_refl (term332 A x f t' t)). Qed.
Lemma lem7061022 {A : Type'} (x : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term334 A x f t') = (term327 A x f t').
Proof. exact (fun_ext (fun t : A -> Prop => @lem7061021 A x f t' t)). Qed.
Lemma lem7061023 {A : Type'} (t : A -> Prop) (x : A -> Prop) : (@INTER A t x) = (@INTER A t x).
Proof. exact (eq_refl (@INTER A t x)). Qed.
Lemma lem7061024 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term331 A f t' t x) = (term329 A f t' t x).
Proof. exact (MK_COMB (@lem7061022 A x f t') (@lem7061023 A t x)). Qed.
Lemma lem7061025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7061026 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term335 A f t' t x) = (term336 A f t' t x).
Proof. exact (MK_COMB (@lem7061025) (@lem7061024 A f t' t x)). Qed.
Lemma lem7061027 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term329 A f t' t x) = (term337 A f t' t x).
Proof. exact (eq_refl (term329 A f t' t x)). Qed.
Lemma lem7061028 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : ((term331 A f t' t x) = (term329 A f t' t x)) = ((term329 A f t' t x) = (term337 A f t' t x)).
Proof. exact (MK_COMB (@lem7061026 A f t' t x) (@lem7061027 A f t' t x)). Qed.
Lemma lem7061029 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term329 A f t' t x) = (term337 A f t' t x).
Proof. exact (EQ_MP (@lem7061028 A f t' t x) (@lem7061020 A f t' t x)). Qed.
Lemma lem7061034 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term328 A t' f t x) = (term337 A f t' t x).
Proof. exact (TRANS (@lem7061016 A f t' t x) (@lem7061029 A f t' t x)). Qed.
Lemma lem7061035 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term338 A t' f t) = (term339 A f t' t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem7061034 A f t' t x)). Qed.
Lemma lem7061036 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7061037 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term316 A t' f t) = (term340 A f t' t).
Proof. exact (MK_COMB (@lem7061036 A) (@lem7061035 A f t' t)). Qed.
Lemma lem7061042 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term313 A t' f t) = (term340 A f t' t).
Proof. exact (TRANS (@lem7060993 A t' f t) (@lem7061037 A f t' t)). Qed.
Lemma lem7061043 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7061044 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term341 A t' f t) = (term342 A f t' t).
Proof. exact (MK_COMB (@lem7061043) (@lem7061042 A f t' t)). Qed.
Lemma lem7061047 {A : Type'} (t' : A -> Prop) : (t' = (@EMPTY A)) = (t' = (@EMPTY A)).
Proof. exact (eq_refl (t' = (@EMPTY A))). Qed.
Lemma lem7061048 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term343 A f t t') = (term344 A f t t').
Proof. exact (MK_COMB (@lem7061044 A f t' t) (@lem7061047 A t')). Qed.
Lemma lem7061051 {A : Type'} (f : type686 A) (t : A -> Prop) : (term345 A f t) = (term346 A f t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7061048 A f t t')). Qed.
Lemma lem7061052 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061053 {A : Type'} (f : type686 A) (t : A -> Prop) : (term301 A f t) = (term347 A f t).
Proof. exact (MK_COMB (@lem7061052 A) (@lem7061051 A f t)). Qed.
Lemma lem7061058 {A : Type'} (f : type686 A) (t : A -> Prop) : ((term276 A f t) = (@EMPTY A)) = (term347 A f t).
Proof. exact (TRANS (@lem7060970 A f t) (@lem7061053 A f t)). Qed.
Lemma lem7061059 {A : Type'} (f : type686 A) (t : A -> Prop) : (term347 A f t) = ((term276 A f t) = (@EMPTY A)).
Proof. exact (SYM (@lem7061058 A f t)). Qed.
Lemma lem7061060 (t1 : Prop) : term348 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7061061 (t1 : Prop) : (term348 t1) = (term349 t1).
Proof. exact (eq_refl (term348 t1)). Qed.
Lemma lem7061062 (t1 : Prop) : term349 t1.
Proof. exact (EQ_MP (@lem7061061 t1) (@lem7061060 t1)). Qed.
Lemma lem7061063 (t1 : Prop) (t2 : Prop) : term350 t1 t2.
Proof. exact (@lem7061062 t1 t2). Qed.
Lemma lem7061064 (t1 : Prop) (t2 : Prop) : (term350 t1 t2) = (term351 t1 t2).
Proof. exact (eq_refl (term350 t1 t2)). Qed.
Lemma lem7061065 (t1 : Prop) (t2 : Prop) : term351 t1 t2.
Proof. exact (EQ_MP (@lem7061064 t1 t2) (@lem7061063 t1 t2)). Qed.
Lemma lem7061066 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term352 t1 t2 t3.
Proof. exact (@lem7061065 t1 t2 t3). Qed.
Lemma lem7061067 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term352 t1 t2 t3) = ((term353 t1 t2 t3) = (term354 t1 t2 t3)).
Proof. exact (eq_refl (term352 t1 t2 t3)). Qed.
Lemma lem7061068 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term353 t1 t2 t3) = (term354 t1 t2 t3).
Proof. exact (EQ_MP (@lem7061067 t1 t2 t3) (@lem7061066 t1 t2 t3)). Qed.
Lemma lem7061069 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term354 t1 t2 t3) = (term353 t1 t2 t3).
Proof. exact (SYM (@lem7061068 t1 t2 t3)). Qed.
Lemma lem7061071 (p : Prop) : p = (term355 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7061072 {A : Type'} (f : type686 A) (t : A -> Prop) : (term347 A f t) = (term356 A f t).
Proof. exact (@lem7061071 (term347 A f t)). Qed.
Lemma lem7061073 {A : Type'} (f : type686 A) (t : A -> Prop) : (term356 A f t) = (term347 A f t).
Proof. exact (SYM (@lem7061072 A f t)). Qed.
Lemma lem7061074 {A : Type'} (f : type686 A) (t : A -> Prop) (h1 : term357 A f t) : term357 A f t.
Proof. exact (h1). Qed.
Lemma lem7061077 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term358 A t f) : term358 A t f.
Proof. exact (h1). Qed.
Lemma lem7061078 {A : Type'} (t : A -> Prop) (f : type686 A) : term359 A t f.
Proof. exact (fun h0 : term358 A t f => @lem7061077 A t f h0). Qed.
Lemma lem7061079 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term359 A t f) : term359 A t f.
Proof. exact (h1). Qed.
Lemma lem7061080 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term358 A t f) : term358 A t f.
Proof. exact (h1). Qed.
Lemma lem7061081 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term358 A t f) (h2 : term359 A t f) : term358 A t f.
Proof. exact (@lem7061079 A t f h2 (@lem7061080 A t f h1)). Qed.
Lemma lem7061082 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term358 A t f) : term360 A t f.
Proof. exact (fun h0 : term359 A t f => @lem7061081 A t f h1 h0). Qed.
Lemma lem7061083 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term359 A t f) : term359 A t f.
Proof. exact (h1). Qed.
Lemma lem7061084 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term358 A t f) (h2 : term359 A t f) : term358 A t f.
Proof. exact (@lem7061082 A t f h1 (@lem7061083 A t f h2)). Qed.
Lemma lem7061085 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term359 A t f) : term359 A t f.
Proof. exact (fun h0 : term358 A t f => @lem7061084 A t f h0 h1). Qed.
Lemma lem7061086 {A : Type'} (t : A -> Prop) (f : type686 A) : term361 A t f.
Proof. exact (fun h0 : term359 A t f => @lem7061085 A t f h0). Qed.
Lemma lem7061089 {A : Type'} (t : A -> Prop) (f : type686 A) : term359 A t f.
Proof. exact (@lem7061086 A t f (@lem7061078 A t f)). Qed.
Lemma lem7061090 {A : Type'} (t : A -> Prop) (f : type686 A) : term359 A t f.
Proof. exact (@lem7061089 A t f). Qed.
Lemma lem7061190 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7061191 {A : Type'} (f : type686 A) : (term362 A f) = (term363 A f).
Proof. exact (@lem7061190 (@FINITE (A -> Prop) f)). Qed.
Lemma lem7061192 {A : Type'} (t : A -> Prop) (f : type686 A) : (term364 A t f) = (term364 A t f).
Proof. exact (eq_refl (term364 A t f)). Qed.
Lemma lem7061193 {A : Type'} (t : A -> Prop) (f : type686 A) : (term365 A t f) = (term366 A t f).
Proof. exact (MK_COMB (@lem7061192 A t f) (@lem7061191 A f)). Qed.
Lemma lem7061196 {A : Type'} (t : A -> Prop) (f : type686 A) : (term367 A t f) = (term367 A t f).
Proof. exact (eq_refl (term367 A t f)). Qed.
Lemma lem7061197 {A : Type'} (t : A -> Prop) (f : type686 A) : (term368 A t f) = (term369 A t f).
Proof. exact (MK_COMB (@lem7061196 A t f) (@lem7061193 A t f)). Qed.
Lemma lem7061200 {A : Type'} (t : A -> Prop) (f : type686 A) : (term370 A t f) = (term370 A t f).
Proof. exact (eq_refl (term370 A t f)). Qed.
Lemma lem7061201 {A : Type'} (t : A -> Prop) (f : type686 A) : (term371 A t f) = (term372 A t f).
Proof. exact (MK_COMB (@lem7061200 A t f) (@lem7061197 A t f)). Qed.
Lemma lem7061204 {A : Type'} (f : type686 A) (t : A -> Prop) : (term373 A f t) = (term373 A f t).
Proof. exact (eq_refl (term373 A f t)). Qed.
Lemma lem7061205 {A : Type'} (t : A -> Prop) (f : type686 A) : (term358 A t f) = (term374 A t f).
Proof. exact (MK_COMB (@lem7061204 A f t) (@lem7061201 A t f)). Qed.
Lemma lem7061208 {A : Type'} (f : type686 A) : (term375 A f) = (term376 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7061205 A t f)). Qed.
Lemma lem7061209 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061210 {A : Type'} (f : type686 A) : (term377 A f) = (term378 A f).
Proof. exact (MK_COMB (@lem7061209 A) (@lem7061208 A f)). Qed.
Lemma lem7061215 {A : Type'} : (term379 A) = (term380 A).
Proof. exact (fun_ext (fun f : type686 A => @lem7061210 A f)). Qed.
Lemma lem7061216 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7061225 {A : Type'} : (term381 A) = (term382 A).
Proof. exact (MK_COMB (@lem7061216 A) (@lem7061215 A)). Qed.
Lemma lem7061234 {A : Type'} (t : A -> Prop) (f : type686 A) : (term366 A t f) = (term366 A t f).
Proof. exact (eq_refl (term366 A t f)). Qed.
Lemma lem7061257 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term135 A t f t' u) = (term135 A t f t' u).
Proof. exact (eq_refl (term135 A t f t' u)). Qed.
Lemma lem7061258 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term137 A t f t') = (term137 A t f t').
Proof. exact (fun_ext (fun u : A -> Prop => @lem7061257 A t f t' u)). Qed.
Lemma lem7061259 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061260 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term139 A t f t') = (term139 A t f t').
Proof. exact (MK_COMB (@lem7061259 A) (@lem7061258 A t f t')). Qed.
Lemma lem7061261 {A : Type'} (t : A -> Prop) (f : type686 A) : (term141 A t f) = (term141 A t f).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7061260 A t f t')). Qed.
Lemma lem7061262 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061263 {A : Type'} (t : A -> Prop) (f : type686 A) : (term143 A t f) = (term143 A t f).
Proof. exact (MK_COMB (@lem7061262 A) (@lem7061261 A t f)). Qed.
Lemma lem7061264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7061265 {A : Type'} (t : A -> Prop) (f : type686 A) : (term367 A t f) = (term367 A t f).
Proof. exact (MK_COMB (@lem7061264) (@lem7061263 A t f)). Qed.
Lemma lem7061266 {A : Type'} (t : A -> Prop) (f : type686 A) : (term369 A t f) = (term369 A t f).
Proof. exact (MK_COMB (@lem7061265 A t f) (@lem7061234 A t f)). Qed.
Lemma lem7061275 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term119 A t f t') = (term119 A t f t').
Proof. exact (eq_refl (term119 A t f t')). Qed.
Lemma lem7061276 {A : Type'} (t : A -> Prop) (f : type686 A) : (term121 A t f) = (term121 A t f).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7061275 A t f t')). Qed.
Lemma lem7061277 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061278 {A : Type'} (t : A -> Prop) (f : type686 A) : (term123 A t f) = (term123 A t f).
Proof. exact (MK_COMB (@lem7061277 A) (@lem7061276 A t f)). Qed.
Lemma lem7061279 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7061280 {A : Type'} (t : A -> Prop) (f : type686 A) : (term370 A t f) = (term370 A t f).
Proof. exact (MK_COMB (@lem7061279) (@lem7061278 A t f)). Qed.
Lemma lem7061281 {A : Type'} (t : A -> Prop) (f : type686 A) : (term372 A t f) = (term372 A t f).
Proof. exact (MK_COMB (@lem7061280 A t f) (@lem7061266 A t f)). Qed.
Lemma lem7061282 {A : Type'} (t' : A -> Prop) : (t' = (@EMPTY A)) = (t' = (@EMPTY A)).
Proof. exact (eq_refl (t' = (@EMPTY A))). Qed.
Lemma lem7061287 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term337 A f t' t x) = (term337 A f t' t x).
Proof. exact (eq_refl (term337 A f t' t x)). Qed.
Lemma lem7061288 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term339 A f t' t) = (term339 A f t' t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem7061287 A f t' t x)). Qed.
Lemma lem7061289 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7061290 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term340 A f t' t) = (term340 A f t' t).
Proof. exact (MK_COMB (@lem7061289 A) (@lem7061288 A f t' t)). Qed.
Lemma lem7061291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7061292 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term342 A f t' t) = (term342 A f t' t).
Proof. exact (MK_COMB (@lem7061291) (@lem7061290 A f t' t)). Qed.
Lemma lem7061293 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term344 A f t t') = (term344 A f t t').
Proof. exact (MK_COMB (@lem7061292 A f t' t) (@lem7061282 A t')). Qed.
Lemma lem7061294 {A : Type'} (f : type686 A) (t : A -> Prop) : (term346 A f t) = (term346 A f t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7061293 A f t t')). Qed.
Lemma lem7061295 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061296 {A : Type'} (f : type686 A) (t : A -> Prop) : (term347 A f t) = (term347 A f t).
Proof. exact (MK_COMB (@lem7061295 A) (@lem7061294 A f t)). Qed.
Lemma lem7061297 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7061298 {A : Type'} (f : type686 A) (t : A -> Prop) : (term357 A f t) = (term357 A f t).
Proof. exact (MK_COMB (@lem7061297) (@lem7061296 A f t)). Qed.
Lemma lem7061299 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7061300 {A : Type'} (f : type686 A) (t : A -> Prop) : (term373 A f t) = (term373 A f t).
Proof. exact (MK_COMB (@lem7061299) (@lem7061298 A f t)). Qed.
Lemma lem7061301 {A : Type'} (t : A -> Prop) (f : type686 A) : (term374 A t f) = (term374 A t f).
Proof. exact (MK_COMB (@lem7061300 A f t) (@lem7061281 A t f)). Qed.
Lemma lem7061302 {A : Type'} (f : type686 A) : (term376 A f) = (term376 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7061301 A t f)). Qed.
Lemma lem7061303 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061304 {A : Type'} (f : type686 A) : (term378 A f) = (term378 A f).
Proof. exact (MK_COMB (@lem7061303 A) (@lem7061302 A f)). Qed.
Lemma lem7061305 {A : Type'} : (term380 A) = (term380 A).
Proof. exact (fun_ext (fun f : type686 A => @lem7061304 A f)). Qed.
Lemma lem7061306 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7061307 {A : Type'} : (term382 A) = (term382 A).
Proof. exact (MK_COMB (@lem7061306 A) (@lem7061305 A)). Qed.
Lemma lem7061378 {A : Type'} : (term381 A) = (term382 A).
Proof. exact (TRANS (@lem7061225 A) (@lem7061307 A)). Qed.
Lemma lem7061379 {A : Type'} : (term382 A) = (term381 A).
Proof. exact (SYM (@lem7061378 A)). Qed.
Lemma lem7061380 {A : Type'} (f : type686 A) (t : A -> Prop) (h1 : term357 A f t) : term357 A f t.
Proof. exact (h1). Qed.
Lemma lem7061382 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term143 A t f.
Proof. exact (h1). Qed.
Lemma lem7061389 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term337 A f t' t x) = (term337 A f t' t x).
Proof. exact (eq_refl (term337 A f t' t x)). Qed.
Lemma lem7061390 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term339 A f t' t) = (term339 A f t' t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem7061389 A f t' t x)). Qed.
Lemma lem7061391 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7061392 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term340 A f t' t) = (term340 A f t' t).
Proof. exact (MK_COMB (@lem7061391 A) (@lem7061390 A f t' t)). Qed.
Lemma lem7061393 {A : Type'} (t' : A -> Prop) : (term383 A t') = (term383 A t').
Proof. exact (eq_refl (term383 A t')). Qed.
Lemma lem7061394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7061395 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term384 A f t' t) = (term384 A f t' t).
Proof. exact (MK_COMB (@lem7061394) (@lem7061392 A f t' t)). Qed.
Lemma lem7061396 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term385 A f t t') = (term385 A f t t').
Proof. exact (MK_COMB (@lem7061395 A f t' t) (@lem7061393 A t')). Qed.
Lemma lem7061397 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term386 A f t t') = (term385 A f t t').
Proof. exact (@lem17362 (term340 A f t' t) (t' = (@EMPTY A))). Qed.
Lemma lem7061398 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term386 A f t t') = (term385 A f t t').
Proof. exact (TRANS (@lem7061397 A f t t') (@lem7061396 A f t t')). Qed.
Lemma lem7061399 {A : Type'} (P : type686 A) : (term387 A P) = (term388 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem7061400 {A : Type'} (f : type686 A) (t : A -> Prop) : (term357 A f t) = (term389 A f t).
Proof. exact (@lem7061399 A (term346 A f t)). Qed.
Lemma lem7061401 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term390 A f t t') = (term344 A f t t').
Proof. exact (eq_refl (term390 A f t t')). Qed.
Lemma lem7061402 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7061403 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term391 A f t t') = (term386 A f t t').
Proof. exact (MK_COMB (@lem7061402) (@lem7061401 A f t t')). Qed.
Lemma lem7061404 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term391 A f t t') = (term385 A f t t').
Proof. exact (TRANS (@lem7061403 A f t t') (@lem7061398 A f t t')). Qed.
Lemma lem7061405 {A : Type'} (f : type686 A) (t : A -> Prop) : (term392 A f t) = (term393 A f t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7061404 A f t t')). Qed.
Lemma lem7061406 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7061407 {A : Type'} (f : type686 A) (t : A -> Prop) : (term389 A f t) = (term394 A f t).
Proof. exact (MK_COMB (@lem7061406 A) (@lem7061405 A f t)). Qed.
Lemma lem7061408 {A : Type'} (f : type686 A) (t : A -> Prop) : (term357 A f t) = (term394 A f t).
Proof. exact (TRANS (@lem7061400 A f t) (@lem7061407 A f t)). Qed.
Lemma lem7061507 {A : Type'} (P : A -> Prop) (Q : Prop) : (term395 A P Q) = (term396 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7061508 {A : Type'} (P : type686 A) (Q : Prop) : (term397 A P Q) = (term398 A P Q).
Proof. exact (@lem7061507 (A -> Prop) P Q). Qed.
Lemma lem7061509 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term399 A f t t') = (term400 A f t t').
Proof. exact (@lem7061508 A (term339 A f t' t) (term383 A t')). Qed.
Lemma lem7061510 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term401 A f t' t x) = (term337 A f t' t x).
Proof. exact (eq_refl (term401 A f t' t x)). Qed.
Lemma lem7061511 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term402 A f t' t) = (term339 A f t' t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem7061510 A f t' t x)). Qed.
Lemma lem7061512 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7061513 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term403 A f t' t) = (term340 A f t' t).
Proof. exact (MK_COMB (@lem7061512 A) (@lem7061511 A f t' t)). Qed.
Lemma lem7061514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7061515 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) : (term404 A f t' t) = (term384 A f t' t).
Proof. exact (MK_COMB (@lem7061514) (@lem7061513 A f t' t)). Qed.
Lemma lem7061516 {A : Type'} (t' : A -> Prop) : (term383 A t') = (term383 A t').
Proof. exact (eq_refl (term383 A t')). Qed.
Lemma lem7061517 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term399 A f t t') = (term385 A f t t').
Proof. exact (MK_COMB (@lem7061515 A f t' t) (@lem7061516 A t')). Qed.
Lemma lem7061518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7061519 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term405 A f t t') = (term406 A f t t').
Proof. exact (MK_COMB (@lem7061518) (@lem7061517 A f t t')). Qed.
Lemma lem7061520 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term401 A f t' t x) = (term337 A f t' t x).
Proof. exact (eq_refl (term401 A f t' t x)). Qed.
Lemma lem7061521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7061522 {A : Type'} (f : type686 A) (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : (term407 A f t' t x) = (term408 A f t' t x).
Proof. exact (MK_COMB (@lem7061521) (@lem7061520 A f t' t x)). Qed.
Lemma lem7061523 {A : Type'} (t' : A -> Prop) : (term383 A t') = (term383 A t').
Proof. exact (eq_refl (term383 A t')). Qed.
Lemma lem7061524 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) : (term409 A f t x t') = (term410 A f t x t').
Proof. exact (MK_COMB (@lem7061522 A f t' t x) (@lem7061523 A t')). Qed.
Lemma lem7061525 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term411 A f t t') = (term412 A f t t').
Proof. exact (fun_ext (fun x : A -> Prop => @lem7061524 A f t x t')). Qed.
Lemma lem7061526 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7061527 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term400 A f t t') = (term413 A f t t').
Proof. exact (MK_COMB (@lem7061526 A) (@lem7061525 A f t t')). Qed.
Lemma lem7061528 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : ((term399 A f t t') = (term400 A f t t')) = ((term385 A f t t') = (term413 A f t t')).
Proof. exact (MK_COMB (@lem7061519 A f t t') (@lem7061527 A f t t')). Qed.
Lemma lem7061529 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) : (term385 A f t t') = (term413 A f t t').
Proof. exact (EQ_MP (@lem7061528 A f t t') (@lem7061509 A f t t')). Qed.
Lemma lem7061530 {A : Type'} (f : type686 A) (t : A -> Prop) : (term393 A f t) = (term414 A f t).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7061529 A f t t')). Qed.
Lemma lem7061531 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7061533 {A : Type'} (f : type686 A) (t : A -> Prop) : (term394 A f t) = (term415 A f t).
Proof. exact (MK_COMB (@lem7061531 A) (@lem7061530 A f t)). Qed.
Lemma lem7061534 {A : Type'} (f : type686 A) (t : A -> Prop) : (term357 A f t) = (term415 A f t).
Proof. exact (TRANS (@lem7061408 A f t) (@lem7061533 A f t)). Qed.
Lemma lem7061535 {A : Type'} (f : type686 A) (t : A -> Prop) (h1 : term357 A f t) : term415 A f t.
Proof. exact (EQ_MP (@lem7061534 A f t) (@lem7061380 A f t h1)). Qed.
Lemma lem7061595 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (f : type686 A) : (term416 A t t' f) = (term417 A t t' f).
Proof. exact (@lem17160 (t' = t) (@IN (A -> Prop) t' f)). Qed.
Lemma lem7061602 {A : Type'} (t : A -> Prop) (u : A -> Prop) (f : type686 A) : (term416 A t u f) = (term417 A t u f).
Proof. exact (@lem17160 (u = t) (@IN (A -> Prop) u f)). Qed.
Lemma lem7061605 {A : Type'} (t' : A -> Prop) (u : A -> Prop) : (term418 A t' u) = (t' = u).
Proof. exact (@lem16933 (t' = u)). Qed.
Lemma lem7061606 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7061607 {A : Type'} (t : A -> Prop) (u : A -> Prop) (f : type686 A) : (term419 A t u f) = (term420 A t u f).
Proof. exact (MK_COMB (@lem7061606) (@lem7061602 A t u f)). Qed.
Lemma lem7061608 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term421 A t f t' u) = (term422 A t f t' u).
Proof. exact (MK_COMB (@lem7061607 A t u f) (@lem7061605 A t' u)). Qed.
Lemma lem7061609 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term423 A t f t' u) = (term421 A t f t' u).
Proof. exact (@lem17045 (term115 A t u f) (term96 A t' u)). Qed.
Lemma lem7061610 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term423 A t f t' u) = (term422 A t f t' u).
Proof. exact (TRANS (@lem7061609 A t f t' u) (@lem7061608 A t f t' u)). Qed.
Lemma lem7061611 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7061612 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (f : type686 A) : (term419 A t t' f) = (term420 A t t' f).
Proof. exact (MK_COMB (@lem7061611) (@lem7061595 A t t' f)). Qed.
Lemma lem7061613 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term424 A t f t' u) = (term425 A t f t' u).
Proof. exact (MK_COMB (@lem7061612 A t t' f) (@lem7061610 A t f t' u)). Qed.
Lemma lem7061614 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term426 A t f t' u) = (term424 A t f t' u).
Proof. exact (@lem17045 (term115 A t t' f) (term129 A t f t' u)). Qed.
Lemma lem7061615 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term426 A t f t' u) = (term425 A t f t' u).
Proof. exact (TRANS (@lem7061614 A t f t' u) (@lem7061613 A t f t' u)). Qed.
Lemma lem7061616 {A : Type'} (t' : A -> Prop) (u : A -> Prop) : ((@INTER A t' u) = (@EMPTY A)) = ((@INTER A t' u) = (@EMPTY A)).
Proof. exact (eq_refl ((@INTER A t' u) = (@EMPTY A))). Qed.
Lemma lem7061617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7061618 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term427 A t f t' u) = (term428 A t f t' u).
Proof. exact (MK_COMB (@lem7061617) (@lem7061615 A t f t' u)). Qed.
Lemma lem7061619 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term429 A t f t' u) = (term430 A t f t' u).
Proof. exact (MK_COMB (@lem7061618 A t f t' u) (@lem7061616 A t' u)). Qed.
Lemma lem7061620 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term135 A t f t' u) = (term429 A t f t' u).
Proof. exact (@lem17265 (term131 A t f t' u) ((@INTER A t' u) = (@EMPTY A))). Qed.
Lemma lem7061621 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term135 A t f t' u) = (term430 A t f t' u).
Proof. exact (TRANS (@lem7061620 A t f t' u) (@lem7061619 A t f t' u)). Qed.
Lemma lem7061622 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term137 A t f t') = (term431 A t f t').
Proof. exact (fun_ext (fun u : A -> Prop => @lem7061621 A t f t' u)). Qed.
Lemma lem7061623 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061624 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term139 A t f t') = (term432 A t f t').
Proof. exact (MK_COMB (@lem7061623 A) (@lem7061622 A t f t')). Qed.
Lemma lem7061625 {A : Type'} (t : A -> Prop) (f : type686 A) : (term141 A t f) = (term433 A t f).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7061624 A t f t')). Qed.
Lemma lem7061626 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061683 {A : Type'} (t : A -> Prop) (f : type686 A) : (term143 A t f) = (term434 A t f).
Proof. exact (MK_COMB (@lem7061626 A) (@lem7061625 A t f)). Qed.
Lemma lem7061684 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term434 A t f.
Proof. exact (EQ_MP (@lem7061683 A t f) (@lem7061382 A t f h1)). Qed.
Lemma lem7061690 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : term234 A t f.
Proof. exact (h1). Qed.
Lemma lem7061697 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) (h1 : term413 A f t t') : term413 A f t t'.
Proof. exact (h1). Qed.
Lemma lem7061782 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term430 A t f t' u) = (term430 A t f t' u).
Proof. exact (eq_refl (term430 A t f t' u)). Qed.
Lemma lem7061783 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term431 A t f t') = (term431 A t f t').
Proof. exact (fun_ext (fun u : A -> Prop => @lem7061782 A t f t' u)). Qed.
Lemma lem7061784 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061785 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term432 A t f t') = (term432 A t f t').
Proof. exact (MK_COMB (@lem7061784 A) (@lem7061783 A t f t')). Qed.
Lemma lem7061786 {A : Type'} (t : A -> Prop) (f : type686 A) : (term433 A t f) = (term433 A t f).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7061785 A t f t')). Qed.
Lemma lem7061787 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061788 {A : Type'} (t : A -> Prop) (f : type686 A) : (term434 A t f) = (term434 A t f).
Proof. exact (MK_COMB (@lem7061787 A) (@lem7061786 A t f)). Qed.
Lemma lem7061789 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term434 A t f.
Proof. exact (EQ_MP (@lem7061788 A t f) (@lem7061684 A t f h1)). Qed.
Lemma lem7061797 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : term234 A t f.
Proof. exact (h1). Qed.
Lemma lem7061829 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : term410 A f t x t'.
Proof. exact (h1). Qed.
Lemma lem7061831 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : term337 A f t' t x.
Proof. exact (proj1 (@lem7061829 A f t x t' h1)). Qed.
Lemma lem7061858 {A : Type'} (t' : A -> Prop) (u : A -> Prop) : ((@INTER A t' u) = (@EMPTY A)) = ((@INTER A t' u) = (@EMPTY A)).
Proof. exact (eq_refl ((@INTER A t' u) = (@EMPTY A))). Qed.
Lemma lem7061875 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term422 A t f t' u) = (term435 A t f t' u).
Proof. exact (@lem19699 (term96 A u t) (term234 A u f) (t' = u)). Qed.
Lemma lem7061882 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (f : type686 A) : (term420 A t t' f) = (term420 A t t' f).
Proof. exact (eq_refl (term420 A t t' f)). Qed.
Lemma lem7061883 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term425 A t f t' u) = (term436 A t f t' u).
Proof. exact (MK_COMB (@lem7061882 A t t' f) (@lem7061875 A t f t' u)). Qed.
Lemma lem7061884 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term436 A t f t' u) = (term437 A t f t' u).
Proof. exact (@lem19490 (term438 A t t' u) (term417 A t t' f) (term439 A f t' u)). Qed.
Lemma lem7061891 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term440 A t f t' u) = (term441 A t f t' u).
Proof. exact (@lem19699 (term96 A t' t) (term234 A t' f) (term439 A f t' u)). Qed.
Lemma lem7061898 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) (u : A -> Prop) : (term442 A f t t' u) = (term443 A f t t' u).
Proof. exact (@lem19699 (term96 A t' t) (term234 A t' f) (term438 A t t' u)). Qed.
Lemma lem7061899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7061900 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) (u : A -> Prop) : (term444 A f t t' u) = (term445 A f t t' u).
Proof. exact (MK_COMB (@lem7061899) (@lem7061898 A f t t' u)). Qed.
Lemma lem7061901 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term437 A t f t' u) = (term446 A t f t' u).
Proof. exact (MK_COMB (@lem7061900 A f t t' u) (@lem7061891 A t f t' u)). Qed.
Lemma lem7061902 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term436 A t f t' u) = (term446 A t f t' u).
Proof. exact (TRANS (@lem7061884 A t f t' u) (@lem7061901 A t f t' u)). Qed.
Lemma lem7061903 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term425 A t f t' u) = (term446 A t f t' u).
Proof. exact (TRANS (@lem7061883 A t f t' u) (@lem7061902 A t f t' u)). Qed.
Lemma lem7061904 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7061905 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term428 A t f t' u) = (term447 A t f t' u).
Proof. exact (MK_COMB (@lem7061904) (@lem7061903 A t f t' u)). Qed.
Lemma lem7061906 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term430 A t f t' u) = (term448 A t f t' u).
Proof. exact (MK_COMB (@lem7061905 A t f t' u) (@lem7061858 A t' u)). Qed.
Lemma lem7061907 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term448 A t f t' u) = (term449 A t f t' u).
Proof. exact (@lem19699 (term443 A f t t' u) (term441 A t f t' u) ((@INTER A t' u) = (@EMPTY A))). Qed.
Lemma lem7061914 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term450 A t f t' u) = (term451 A t f t' u).
Proof. exact (@lem19699 (term452 A t f t' u) (term453 A f t' u) ((@INTER A t' u) = (@EMPTY A))). Qed.
Lemma lem7061921 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) (u : A -> Prop) : (term454 A f t t' u) = (term455 A f t t' u).
Proof. exact (@lem19699 (term456 A t t' u) (term457 A f t t' u) ((@INTER A t' u) = (@EMPTY A))). Qed.
Lemma lem7061922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7061923 {A : Type'} (f : type686 A) (t : A -> Prop) (t' : A -> Prop) (u : A -> Prop) : (term458 A f t t' u) = (term459 A f t t' u).
Proof. exact (MK_COMB (@lem7061922) (@lem7061921 A f t t' u)). Qed.
Lemma lem7061924 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term449 A t f t' u) = (term460 A t f t' u).
Proof. exact (MK_COMB (@lem7061923 A f t t' u) (@lem7061914 A t f t' u)). Qed.
Lemma lem7061925 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term448 A t f t' u) = (term460 A t f t' u).
Proof. exact (TRANS (@lem7061907 A t f t' u) (@lem7061924 A t f t' u)). Qed.
Lemma lem7061926 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) (u : A -> Prop) : (term430 A t f t' u) = (term460 A t f t' u).
Proof. exact (TRANS (@lem7061906 A t f t' u) (@lem7061925 A t f t' u)). Qed.
Lemma lem7061927 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term431 A t f t') = (term461 A t f t').
Proof. exact (fun_ext (fun u : A -> Prop => @lem7061926 A t f t' u)). Qed.
Lemma lem7061928 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061929 {A : Type'} (t : A -> Prop) (f : type686 A) (t' : A -> Prop) : (term432 A t f t') = (term462 A t f t').
Proof. exact (MK_COMB (@lem7061928 A) (@lem7061927 A t f t')). Qed.
Lemma lem7061930 {A : Type'} (t : A -> Prop) (f : type686 A) : (term433 A t f) = (term463 A t f).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7061929 A t f t')). Qed.
Lemma lem7061931 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7061933 {A : Type'} (t : A -> Prop) (f : type686 A) : (term434 A t f) = (term464 A t f).
Proof. exact (MK_COMB (@lem7061931 A) (@lem7061930 A t f)). Qed.
Lemma lem7061934 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term464 A t f.
Proof. exact (EQ_MP (@lem7061933 A t f) (@lem7061789 A t f h1)). Qed.
Lemma lem7061938 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : term234 A t f.
Proof. exact (h1). Qed.
Lemma lem7061958 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term465 A t f _94252.
Proof. exact (@lem7061934 A t f h1 _94252). Qed.
Lemma lem7061959 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) : (term465 A t f _94252) = (term462 A t f _94252).
Proof. exact (eq_refl (term465 A t f _94252)). Qed.
Lemma lem7061960 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term462 A t f _94252.
Proof. exact (EQ_MP (@lem7061959 A t f _94252) (@lem7061958 A _94252 t f h1)). Qed.
Lemma lem7061961 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term466 A t f _94252 _94253.
Proof. exact (@lem7061960 A _94252 t f h1 _94253). Qed.
Lemma lem7061962 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term466 A t f _94252 _94253) = (term460 A t f _94252 _94253).
Proof. exact (eq_refl (term466 A t f _94252 _94253)). Qed.
Lemma lem7061963 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term460 A t f _94252 _94253.
Proof. exact (EQ_MP (@lem7061962 A t f _94252 _94253) (@lem7061961 A _94252 _94253 t f h1)). Qed.
Lemma lem7061964 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term451 A t f _94252 _94253.
Proof. exact (proj2 (@lem7061963 A _94252 _94253 t f h1)). Qed.
Lemma lem7061967 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term467 A t f _94252 _94253.
Proof. exact (proj1 (@lem7061964 A _94252 _94253 t f h1)). Qed.
Lemma lem7061973 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : term234 A t f.
Proof. exact (h1). Qed.
Lemma lem7061977 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : term383 A t'.
Proof. exact (proj2 (@lem7061829 A f t x t' h1)). Qed.
Lemma lem7061981 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : t' = (@INTER A t x).
Proof. exact (proj2 (@lem7061831 A f t x t' h1)). Qed.
Lemma lem7061985 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term467 A t f _94252 _94253) = (term468 A t f _94252 _94253).
Proof. exact (@lem7061069 (term96 A _94252 t) (term439 A f _94252 _94253) ((@INTER A _94252 _94253) = (@EMPTY A))). Qed.
Lemma lem7061992 {A : Type'} (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term469 A f _94252 _94253) = (term470 A f _94252 _94253).
Proof. exact (@lem7061069 (term234 A _94253 f) (_94252 = _94253) ((@INTER A _94252 _94253) = (@EMPTY A))). Qed.
Lemma lem7061993 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) : (term471 A _94252 t) = (term471 A _94252 t).
Proof. exact (eq_refl (term471 A _94252 t)). Qed.
Lemma lem7061996 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term468 A t f _94252 _94253) = (term472 A t f _94252 _94253).
Proof. exact (MK_COMB (@lem7061993 A _94252 t) (@lem7061992 A f _94252 _94253)). Qed.
Lemma lem7061998 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term467 A t f _94252 _94253) = (term472 A t f _94252 _94253).
Proof. exact (TRANS (@lem7061985 A t f _94252 _94253) (@lem7061996 A t f _94252 _94253)). Qed.
Lemma lem7062093 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : term234 A t f.
Proof. exact (h1). Qed.
Lemma lem7062108 {A : Type'} : (term473 A) = (term473 A).
Proof. exact (eq_refl (term473 A)). Qed.
Lemma lem7062109 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : (term474 A t') = (term475 A t x).
Proof. exact (MK_COMB (@lem7062108 A) (@lem7061981 A f t x t' h1)). Qed.
Lemma lem7062110 {A : Type'} (t : A -> Prop) (x : A -> Prop) : (term475 A t x) = (term476 A t x).
Proof. exact (eq_refl (term475 A t x)). Qed.
Lemma lem7062111 {A : Type'} (t' : A -> Prop) : (term477 A t') = (term477 A t').
Proof. exact (eq_refl (term477 A t')). Qed.
Lemma lem7062112 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : ((term474 A t') = (term475 A t x)) = ((term474 A t') = (term476 A t x)).
Proof. exact (MK_COMB (@lem7062111 A t') (@lem7062110 A t x)). Qed.
Lemma lem7062113 {A : Type'} (t' : A -> Prop) : (term474 A t') = (term383 A t').
Proof. exact (eq_refl (term474 A t')). Qed.
Lemma lem7062114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7062115 {A : Type'} (t' : A -> Prop) : (term477 A t') = (term478 A t').
Proof. exact (MK_COMB (@lem7062114) (@lem7062113 A t')). Qed.
Lemma lem7062116 {A : Type'} (t : A -> Prop) (x : A -> Prop) : (term476 A t x) = (term476 A t x).
Proof. exact (eq_refl (term476 A t x)). Qed.
Lemma lem7062117 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : ((term474 A t') = (term476 A t x)) = ((term383 A t') = (term476 A t x)).
Proof. exact (MK_COMB (@lem7062115 A t') (@lem7062116 A t x)). Qed.
Lemma lem7062118 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (x : A -> Prop) : ((term474 A t') = (term475 A t x)) = ((term383 A t') = (term476 A t x)).
Proof. exact (TRANS (@lem7062112 A t' t x) (@lem7062117 A t' t x)). Qed.
Lemma lem7062119 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : (term383 A t') = (term476 A t x).
Proof. exact (EQ_MP (@lem7062118 A t' t x) (@lem7062109 A f t x t' h1)). Qed.
Lemma lem7062120 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : term476 A t x.
Proof. exact (EQ_MP (@lem7062119 A f t x t' h1) (@lem7061977 A f t x t' h1)). Qed.
Lemma lem7062148 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term472 A t f _94252 _94253.
Proof. exact (EQ_MP (@lem7061998 A t f _94252 _94253) (@lem7061967 A _94252 _94253 t f h1)). Qed.
Lemma lem7062243 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem7062244 {A : Type'} (_94280 : A -> Prop) (_94282 : A -> Prop) (h1 : _94280 = _94282) : _94280 = _94282.
Proof. exact (h1). Qed.
Lemma lem7062245 {A : Type'} (_94281 : type686 A) (_94283 : type686 A) (h1 : _94281 = _94283) : _94281 = _94283.
Proof. exact (h1). Qed.
Lemma lem7062246 {A : Type'} (_94280 : A -> Prop) (_94282 : A -> Prop) (h1 : _94280 = _94282) : (@IN (A -> Prop) _94280) = (@IN (A -> Prop) _94282).
Proof. exact (MK_COMB (@lem7062243 A) (@lem7062244 A _94280 _94282 h1)). Qed.
Lemma lem7062247 {A : Type'} (_94280 : A -> Prop) (_94282 : A -> Prop) (_94281 : type686 A) (_94283 : type686 A) (h1 : _94280 = _94282) (h2 : _94281 = _94283) : (@IN (A -> Prop) _94280 _94281) = (@IN (A -> Prop) _94282 _94283).
Proof. exact (MK_COMB (@lem7062246 A _94280 _94282 h1) (@lem7062245 A _94281 _94283 h2)). Qed.
Lemma lem7062249 (b : Prop) (a : Prop) : term479 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7062250 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : term480 A _94282 _94283 _94280 _94281.
Proof. exact (@lem7062249 (@IN (A -> Prop) _94282 _94283) (@IN (A -> Prop) _94280 _94281)). Qed.
Lemma lem7062251 {A : Type'} (_94280 : A -> Prop) (_94282 : A -> Prop) (_94281 : type686 A) (_94283 : type686 A) (h1 : _94280 = _94282) (h2 : _94281 = _94283) : term481 A _94282 _94283 _94280 _94281.
Proof. exact (@lem7062250 A _94282 _94283 _94280 _94281 (@lem7062247 A _94280 _94282 _94281 _94283 h1 h2)). Qed.
Lemma lem7062252 {A : Type'} (_94283 : type686 A) (_94281 : type686 A) (_94280 : A -> Prop) (_94282 : A -> Prop) (h1 : _94280 = _94282) : term482 A _94282 _94283 _94280 _94281.
Proof. exact (fun h0 : _94281 = _94283 => @lem7062251 A _94280 _94282 _94281 _94283 h1 h0). Qed.
Lemma lem7062254 (a : Prop) (b : Prop) : (a -> b) = (term483 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7062255 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : (term482 A _94282 _94283 _94280 _94281) = (term484 A _94282 _94283 _94280 _94281).
Proof. exact (@lem7062254 (_94281 = _94283) (term481 A _94282 _94283 _94280 _94281)). Qed.
Lemma lem7062256 {A : Type'} (_94283 : type686 A) (_94281 : type686 A) (_94280 : A -> Prop) (_94282 : A -> Prop) (h1 : _94280 = _94282) : term484 A _94282 _94283 _94280 _94281.
Proof. exact (EQ_MP (@lem7062255 A _94282 _94283 _94280 _94281) (@lem7062252 A _94283 _94281 _94280 _94282 h1)). Qed.
Lemma lem7062257 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : term485 A _94282 _94283 _94280 _94281.
Proof. exact (fun h0 : _94280 = _94282 => @lem7062256 A _94283 _94281 _94280 _94282 h0). Qed.
Lemma lem7062259 (a : Prop) (b : Prop) : (a -> b) = (term483 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7062260 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : (term485 A _94282 _94283 _94280 _94281) = (term486 A _94282 _94283 _94280 _94281).
Proof. exact (@lem7062259 (_94280 = _94282) (term484 A _94282 _94283 _94280 _94281)). Qed.
Lemma lem7062261 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : term486 A _94282 _94283 _94280 _94281.
Proof. exact (EQ_MP (@lem7062260 A _94282 _94283 _94280 _94281) (@lem7062257 A _94282 _94283 _94280 _94281)). Qed.
Lemma lem7062278 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term487 A x y z.
Proof. exact (@lem21385 (A -> Prop) x y z). Qed.
Lemma lem7062282 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem7062283 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem7062282 A x). Qed.
Lemma lem7062284 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (@lem7062283 A t). Qed.
Lemma lem7062285 {A : Type'} (t : A -> Prop) : term488 A t.
Proof. exact (fun h0 : term489 A t => @lem7062284 A t). Qed.
Lemma lem7062287 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7062288 {A : Type'} (t : A -> Prop) : (term488 A t) = (t = t).
Proof. exact (@lem7062287 (t = t)). Qed.
Lemma lem7062289 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (EQ_MP (@lem7062288 A t) (@lem7062285 A t)). Qed.
Lemma lem7062291 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : @IN (A -> Prop) x f.
Proof. exact (proj1 (@lem7061831 A f t x t' h1)). Qed.
Lemma lem7062292 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : term491 A x f.
Proof. exact (fun h0 : term234 A x f => @lem7062291 A f t x t' h1). Qed.
Lemma lem7062294 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7062295 {A : Type'} (x : A -> Prop) (f : type686 A) : (term491 A x f) = (@IN (A -> Prop) x f).
Proof. exact (@lem7062294 (@IN (A -> Prop) x f)). Qed.
Lemma lem7062296 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : @IN (A -> Prop) x f.
Proof. exact (EQ_MP (@lem7062295 A x f) (@lem7062292 A f t x t' h1)). Qed.
Lemma lem7062298 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem7062299 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem7062298 A x). Qed.
Lemma lem7062300 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (@lem7062299 A t). Qed.
Lemma lem7062301 {A : Type'} (t : A -> Prop) : term488 A t.
Proof. exact (fun h0 : term489 A t => @lem7062300 A t). Qed.
Lemma lem7062303 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7062304 {A : Type'} (t : A -> Prop) : (term488 A t) = (t = t).
Proof. exact (@lem7062303 (t = t)). Qed.
Lemma lem7062305 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (EQ_MP (@lem7062304 A t) (@lem7062301 A t)). Qed.
Lemma lem7062307 {A : Type'} (x : type686 A) : x = x.
Proof. exact (@lem21386 (type686 A) x). Qed.
Lemma lem7062308 {A : Type'} (x : type686 A) : x = x.
Proof. exact (@lem7062307 A x). Qed.
Lemma lem7062309 {A : Type'} (f : type686 A) : f = f.
Proof. exact (@lem7062308 A f). Qed.
Lemma lem7062310 {A : Type'} (f : type686 A) : term492 A f.
Proof. exact (fun h0 : term493 A f => @lem7062309 A f). Qed.
Lemma lem7062312 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7062313 {A : Type'} (f : type686 A) : (term492 A f) = (f = f).
Proof. exact (@lem7062312 (f = f)). Qed.
Lemma lem7062314 {A : Type'} (f : type686 A) : f = f.
Proof. exact (EQ_MP (@lem7062313 A f) (@lem7062310 A f)). Qed.
Lemma lem7062316 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : term234 A t f.
Proof. exact (h1). Qed.
Lemma lem7062317 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : term494 A t f.
Proof. exact (fun h0 : @IN (A -> Prop) t f => @lem7062316 A t f h1). Qed.
Lemma lem7062319 (p : Prop) : (term495 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7062320 {A : Type'} (t : A -> Prop) (f : type686 A) : (term494 A t f) = (term234 A t f).
Proof. exact (@lem7062319 (@IN (A -> Prop) t f)). Qed.
Lemma lem7062321 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term234 A t f) : term234 A t f.
Proof. exact (EQ_MP (@lem7062320 A t f) (@lem7062317 A t f h1)). Qed.
Lemma lem7062323 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : @IN (A -> Prop) x f.
Proof. exact (proj1 (@lem7061831 A f t x t' h1)). Qed.
Lemma lem7062324 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : term491 A x f.
Proof. exact (fun h0 : term234 A x f => @lem7062323 A f t x t' h1). Qed.
Lemma lem7062326 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7062327 {A : Type'} (x : A -> Prop) (f : type686 A) : (term491 A x f) = (@IN (A -> Prop) x f).
Proof. exact (@lem7062326 (@IN (A -> Prop) x f)). Qed.
Lemma lem7062328 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : @IN (A -> Prop) x f.
Proof. exact (EQ_MP (@lem7062327 A x f) (@lem7062324 A f t x t' h1)). Qed.
Lemma lem7062330 (b : Prop) (a : Prop) : (a \/ b) = (term496 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7062331 {A : Type'} (_94283 : type686 A) (_94281 : type686 A) (_94280 : A -> Prop) (_94282 : A -> Prop) : (term486 A _94282 _94283 _94280 _94281) = (term497 A _94283 _94281 _94280 _94282).
Proof. exact (@lem7062330 (term484 A _94282 _94283 _94280 _94281) (term96 A _94280 _94282)). Qed.
Lemma lem7062333 (a : Prop) (b : Prop) : (term498 a b) = (term499 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7062334 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : (term500 A _94282 _94283 _94280 _94281) = (term501 A _94282 _94283 _94280 _94281).
Proof. exact (@lem7062333 (term502 A _94281 _94283) (term481 A _94282 _94283 _94280 _94281)). Qed.
Lemma lem7062336 (a : Prop) : (term503 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7062337 {A : Type'} (_94281 : type686 A) (_94283 : type686 A) : (term504 A _94281 _94283) = (_94281 = _94283).
Proof. exact (@lem7062336 (_94281 = _94283)). Qed.
Lemma lem7062338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7062339 {A : Type'} (_94281 : type686 A) (_94283 : type686 A) : (term505 A _94281 _94283) = (term506 A _94281 _94283).
Proof. exact (MK_COMB (@lem7062338) (@lem7062337 A _94281 _94283)). Qed.
Lemma lem7062341 (a : Prop) (b : Prop) : (term498 a b) = (term499 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7062342 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : (term507 A _94282 _94283 _94280 _94281) = (term508 A _94282 _94283 _94280 _94281).
Proof. exact (@lem7062341 (@IN (A -> Prop) _94282 _94283) (term234 A _94280 _94281)). Qed.
Lemma lem7062344 (a : Prop) : (term503 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7062345 {A : Type'} (_94280 : A -> Prop) (_94281 : type686 A) : (term509 A _94280 _94281) = (@IN (A -> Prop) _94280 _94281).
Proof. exact (@lem7062344 (@IN (A -> Prop) _94280 _94281)). Qed.
Lemma lem7062346 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) : (term510 A _94282 _94283) = (term510 A _94282 _94283).
Proof. exact (eq_refl (term510 A _94282 _94283)). Qed.
Lemma lem7062347 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : (term508 A _94282 _94283 _94280 _94281) = (term511 A _94282 _94283 _94280 _94281).
Proof. exact (MK_COMB (@lem7062346 A _94282 _94283) (@lem7062345 A _94280 _94281)). Qed.
Lemma lem7062348 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : (term507 A _94282 _94283 _94280 _94281) = (term511 A _94282 _94283 _94280 _94281).
Proof. exact (TRANS (@lem7062342 A _94282 _94283 _94280 _94281) (@lem7062347 A _94282 _94283 _94280 _94281)). Qed.
Lemma lem7062349 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : (term501 A _94282 _94283 _94280 _94281) = (term512 A _94282 _94283 _94280 _94281).
Proof. exact (MK_COMB (@lem7062339 A _94281 _94283) (@lem7062348 A _94282 _94283 _94280 _94281)). Qed.
Lemma lem7062350 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : (term500 A _94282 _94283 _94280 _94281) = (term512 A _94282 _94283 _94280 _94281).
Proof. exact (TRANS (@lem7062334 A _94282 _94283 _94280 _94281) (@lem7062349 A _94282 _94283 _94280 _94281)). Qed.
Lemma lem7062351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7062352 {A : Type'} (_94282 : A -> Prop) (_94283 : type686 A) (_94280 : A -> Prop) (_94281 : type686 A) : (term513 A _94282 _94283 _94280 _94281) = (term514 A _94282 _94283 _94280 _94281).
Proof. exact (MK_COMB (@lem7062351) (@lem7062350 A _94282 _94283 _94280 _94281)). Qed.
Lemma lem7062353 {A : Type'} (_94280 : A -> Prop) (_94282 : A -> Prop) : (term96 A _94280 _94282) = (term96 A _94280 _94282).
Proof. exact (eq_refl (term96 A _94280 _94282)). Qed.
Lemma lem7062354 {A : Type'} (_94283 : type686 A) (_94281 : type686 A) (_94280 : A -> Prop) (_94282 : A -> Prop) : (term497 A _94283 _94281 _94280 _94282) = (term515 A _94283 _94281 _94280 _94282).
Proof. exact (MK_COMB (@lem7062352 A _94282 _94283 _94280 _94281) (@lem7062353 A _94280 _94282)). Qed.
Lemma lem7062355 {A : Type'} (_94283 : type686 A) (_94281 : type686 A) (_94280 : A -> Prop) (_94282 : A -> Prop) : (term486 A _94282 _94283 _94280 _94281) = (term515 A _94283 _94281 _94280 _94282).
Proof. exact (TRANS (@lem7062331 A _94283 _94281 _94280 _94282) (@lem7062354 A _94283 _94281 _94280 _94282)). Qed.
Lemma lem7062357 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term516 A t x f.
Proof. exact (conj (@lem7062321 A t f h1) (@lem7062328 A f t x t' h2)). Qed.
Lemma lem7062358 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term517 A t x f.
Proof. exact (conj (@lem7062314 A f) (@lem7062357 A f t x t' h1 h2)). Qed.
Lemma lem7062360 {A : Type'} (_94283 : type686 A) (_94281 : type686 A) (_94280 : A -> Prop) (_94282 : A -> Prop) : term515 A _94283 _94281 _94280 _94282.
Proof. exact (EQ_MP (@lem7062355 A _94283 _94281 _94280 _94282) (@lem7062261 A _94282 _94283 _94280 _94281)). Qed.
Lemma lem7062361 {A : Type'} (_94283 : type686 A) (_94281 : type686 A) (_94280 : A -> Prop) (_94282 : A -> Prop) : term515 A _94283 _94281 _94280 _94282.
Proof. exact (@lem7062360 A _94283 _94281 _94280 _94282). Qed.
Lemma lem7062362 {A : Type'} (f : type686 A) (x : A -> Prop) (t : A -> Prop) : term518 A f x t.
Proof. exact (@lem7062361 A f f x t). Qed.
Lemma lem7062365 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term96 A x t.
Proof. exact (@lem7062362 A f x t (@lem7062358 A f t x t' h1 h2)). Qed.
Lemma lem7062366 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term519 A x t.
Proof. exact (fun h0 : x = t => @lem7062365 A f t x t' h1 h2). Qed.
Lemma lem7062368 (p : Prop) : (term495 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7062369 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term519 A x t) = (term96 A x t).
Proof. exact (@lem7062368 (x = t)). Qed.
Lemma lem7062370 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term96 A x t.
Proof. exact (EQ_MP (@lem7062369 A x t) (@lem7062366 A f t x t' h1 h2)). Qed.
Lemma lem7062372 (b : Prop) (a : Prop) : (a \/ b) = (term496 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7062373 {A : Type'} (z : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term487 A x y z) = (term520 A z x y).
Proof. exact (@lem7062372 (term521 A x y z) (term96 A x y)). Qed.
Lemma lem7062375 (a : Prop) (b : Prop) : (term498 a b) = (term499 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7062376 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term522 A x y z) = (term523 A x y z).
Proof. exact (@lem7062375 (term96 A x z) (y = z)). Qed.
Lemma lem7062378 (a : Prop) : (term503 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7062379 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term418 A x z) = (x = z).
Proof. exact (@lem7062378 (x = z)). Qed.
Lemma lem7062380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7062381 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term524 A x z) = (term525 A x z).
Proof. exact (MK_COMB (@lem7062380) (@lem7062379 A x z)). Qed.
Lemma lem7062382 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term96 A y z) = (term96 A y z).
Proof. exact (eq_refl (term96 A y z)). Qed.
Lemma lem7062383 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term523 A x y z) = (term526 A x y z).
Proof. exact (MK_COMB (@lem7062381 A x z) (@lem7062382 A y z)). Qed.
Lemma lem7062384 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term522 A x y z) = (term526 A x y z).
Proof. exact (TRANS (@lem7062376 A x y z) (@lem7062383 A x y z)). Qed.
Lemma lem7062385 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7062386 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term527 A x y z) = (term528 A x y z).
Proof. exact (MK_COMB (@lem7062385) (@lem7062384 A x y z)). Qed.
Lemma lem7062387 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term96 A x y) = (term96 A x y).
Proof. exact (eq_refl (term96 A x y)). Qed.
Lemma lem7062388 {A : Type'} (z : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term520 A z x y) = (term529 A z x y).
Proof. exact (MK_COMB (@lem7062386 A x y z) (@lem7062387 A x y)). Qed.
Lemma lem7062389 {A : Type'} (z : A -> Prop) (x : A -> Prop) (y : A -> Prop) : (term487 A x y z) = (term529 A z x y).
Proof. exact (TRANS (@lem7062373 A z x y) (@lem7062388 A z x y)). Qed.
Lemma lem7062391 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term530 A x t.
Proof. exact (conj (@lem7062305 A t) (@lem7062370 A f t x t' h1 h2)). Qed.
Lemma lem7062393 {A : Type'} (z : A -> Prop) (x : A -> Prop) (y : A -> Prop) : term529 A z x y.
Proof. exact (EQ_MP (@lem7062389 A z x y) (@lem7062278 A x y z)). Qed.
Lemma lem7062394 {A : Type'} (z : A -> Prop) (x : A -> Prop) (y : A -> Prop) : term529 A z x y.
Proof. exact (@lem7062393 A z x y). Qed.
Lemma lem7062395 {A : Type'} (t : A -> Prop) (x : A -> Prop) : term531 A t x.
Proof. exact (@lem7062394 A t t x). Qed.
Lemma lem7062398 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term96 A t x.
Proof. exact (@lem7062395 A t x (@lem7062391 A f t x t' h1 h2)). Qed.
Lemma lem7062399 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term519 A t x.
Proof. exact (fun h0 : t = x => @lem7062398 A f t x t' h1 h2). Qed.
Lemma lem7062401 (p : Prop) : (term495 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7062402 {A : Type'} (t : A -> Prop) (x : A -> Prop) : (term519 A t x) = (term96 A t x).
Proof. exact (@lem7062401 (t = x)). Qed.
Lemma lem7062403 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term96 A t x.
Proof. exact (EQ_MP (@lem7062402 A t x) (@lem7062399 A f t x t' h1 h2)). Qed.
Lemma lem7062421 (q : Prop) (p : Prop) (r : Prop) : (term353 p q r) = (term353 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7062422 {A : Type'} (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term470 A f _94252 _94253) = (term532 A f _94252 _94253).
Proof. exact (@lem7062421 (_94252 = _94253) (term234 A _94253 f) ((@INTER A _94252 _94253) = (@EMPTY A))). Qed.
Lemma lem7062438 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7062439 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term533 A f _94252 _94253) = (term534 A _94252 _94253 f).
Proof. exact (@lem7062438 ((@INTER A _94252 _94253) = (@EMPTY A)) (term234 A _94253 f)). Qed.
Lemma lem7062447 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) : (term197 A _94252 _94253) = (term197 A _94252 _94253).
Proof. exact (eq_refl (term197 A _94252 _94253)). Qed.
Lemma lem7062448 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term532 A f _94252 _94253) = (term535 A _94252 _94253 f).
Proof. exact (MK_COMB (@lem7062447 A _94252 _94253) (@lem7062439 A _94252 _94253 f)). Qed.
Lemma lem7062459 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term470 A f _94252 _94253) = (term535 A _94252 _94253 f).
Proof. exact (TRANS (@lem7062422 A f _94252 _94253) (@lem7062448 A _94252 _94253 f)). Qed.
Lemma lem7062460 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) : (term471 A _94252 t) = (term471 A _94252 t).
Proof. exact (eq_refl (term471 A _94252 t)). Qed.
Lemma lem7062461 {A : Type'} (t : A -> Prop) (_94252 : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term472 A t f _94252 _94253) = (term536 A t _94252 _94253 f).
Proof. exact (MK_COMB (@lem7062460 A _94252 t) (@lem7062459 A _94252 _94253 f)). Qed.
Lemma lem7062465 (q : Prop) (p : Prop) (r : Prop) : (term353 p q r) = (term353 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7062466 {A : Type'} (t : A -> Prop) (_94252 : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term536 A t _94252 _94253 f) = (term537 A t _94252 _94253 f).
Proof. exact (@lem7062465 (_94252 = _94253) (term96 A _94252 t) (term534 A _94252 _94253 f)). Qed.
Lemma lem7062482 (q : Prop) (p : Prop) (r : Prop) : (term353 p q r) = (term353 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7062483 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term538 A t _94252 _94253 f) = (term539 A _94252 t _94253 f).
Proof. exact (@lem7062482 ((@INTER A _94252 _94253) = (@EMPTY A)) (term96 A _94252 t) (term234 A _94253 f)). Qed.
Lemma lem7062503 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) : (term197 A _94252 _94253) = (term197 A _94252 _94253).
Proof. exact (eq_refl (term197 A _94252 _94253)). Qed.
Lemma lem7062504 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term537 A t _94252 _94253 f) = (term540 A _94252 t _94253 f).
Proof. exact (MK_COMB (@lem7062503 A _94252 _94253) (@lem7062483 A _94252 t _94253 f)). Qed.
Lemma lem7062515 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term536 A t _94252 _94253 f) = (term540 A _94252 t _94253 f).
Proof. exact (TRANS (@lem7062466 A t _94252 _94253 f) (@lem7062504 A _94252 t _94253 f)). Qed.
Lemma lem7062516 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term472 A t f _94252 _94253) = (term540 A _94252 t _94253 f).
Proof. exact (TRANS (@lem7062461 A t _94252 _94253 f) (@lem7062515 A _94252 t _94253 f)). Qed.
Lemma lem7062517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7062518 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term541 A t f _94252 _94253) = (term542 A _94252 t _94253 f).
Proof. exact (MK_COMB (@lem7062517) (@lem7062516 A _94252 t _94253 f)). Qed.
Lemma lem7062546 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7062547 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term439 A f _94252 _94253) = (term543 A _94252 _94253 f).
Proof. exact (@lem7062546 (_94252 = _94253) (term234 A _94253 f)). Qed.
Lemma lem7062555 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) : (term471 A _94252 t) = (term471 A _94252 t).
Proof. exact (eq_refl (term471 A _94252 t)). Qed.
Lemma lem7062556 {A : Type'} (t : A -> Prop) (_94252 : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term452 A t f _94252 _94253) = (term544 A t _94252 _94253 f).
Proof. exact (MK_COMB (@lem7062555 A _94252 t) (@lem7062547 A _94252 _94253 f)). Qed.
Lemma lem7062560 (q : Prop) (p : Prop) (r : Prop) : (term353 p q r) = (term353 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7062561 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term544 A t _94252 _94253 f) = (term545 A _94252 t _94253 f).
Proof. exact (@lem7062560 (_94252 = _94253) (term96 A _94252 t) (term234 A _94253 f)). Qed.
Lemma lem7062581 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term452 A t f _94252 _94253) = (term545 A _94252 t _94253 f).
Proof. exact (TRANS (@lem7062556 A t _94252 _94253 f) (@lem7062561 A _94252 t _94253 f)). Qed.
Lemma lem7062582 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) : (term546 A _94252 _94253) = (term546 A _94252 _94253).
Proof. exact (eq_refl (term546 A _94252 _94253)). Qed.
Lemma lem7062583 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term547 A t f _94252 _94253) = (term548 A _94252 t _94253 f).
Proof. exact (MK_COMB (@lem7062582 A _94252 _94253) (@lem7062581 A _94252 t _94253 f)). Qed.
Lemma lem7062587 (q : Prop) (p : Prop) (r : Prop) : (term353 p q r) = (term353 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7062588 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term548 A _94252 t _94253 f) = (term540 A _94252 t _94253 f).
Proof. exact (@lem7062587 (_94252 = _94253) ((@INTER A _94252 _94253) = (@EMPTY A)) (term549 A _94252 t _94253 f)). Qed.
Lemma lem7062620 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : (term547 A t f _94252 _94253) = (term540 A _94252 t _94253 f).
Proof. exact (TRANS (@lem7062583 A _94252 t _94253 f) (@lem7062588 A _94252 t _94253 f)). Qed.
Lemma lem7062621 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : ((term472 A t f _94252 _94253) = (term547 A t f _94252 _94253)) = ((term540 A _94252 t _94253 f) = (term540 A _94252 t _94253 f)).
Proof. exact (MK_COMB (@lem7062518 A _94252 t _94253 f) (@lem7062620 A _94252 t _94253 f)). Qed.
Lemma lem7062623 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7062624 (x : Prop) : (x = x) = True.
Proof. exact (@lem7062623 Prop x). Qed.
Lemma lem7062625 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) (_94253 : A -> Prop) (f : type686 A) : ((term540 A _94252 t _94253 f) = (term540 A _94252 t _94253 f)) = True.
Proof. exact (@lem7062624 (term540 A _94252 t _94253 f)). Qed.
Lemma lem7062626 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : ((term472 A t f _94252 _94253) = (term547 A t f _94252 _94253)) = True.
Proof. exact (TRANS (@lem7062621 A _94252 t _94253 f) (@lem7062625 A _94252 t _94253 f)). Qed.
Lemma lem7062627 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : True = ((term472 A t f _94252 _94253) = (term547 A t f _94252 _94253)).
Proof. exact (SYM (@lem7062626 A t f _94252 _94253)). Qed.
Lemma lem7062628 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term472 A t f _94252 _94253) = (term547 A t f _94252 _94253).
Proof. exact (EQ_MP (@lem7062627 A t f _94252 _94253) (@lem0)). Qed.
Lemma lem7062629 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term547 A t f _94252 _94253.
Proof. exact (EQ_MP (@lem7062628 A t f _94252 _94253) (@lem7062148 A _94252 _94253 t f h1)). Qed.
Lemma lem7062631 (b : Prop) (a : Prop) : (a \/ b) = (term496 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7062632 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term547 A t f _94252 _94253) = (term550 A t f _94252 _94253).
Proof. exact (@lem7062631 (term452 A t f _94252 _94253) ((@INTER A _94252 _94253) = (@EMPTY A))). Qed.
Lemma lem7062634 (a : Prop) (b : Prop) : (term498 a b) = (term499 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7062635 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term551 A t f _94252 _94253) = (term552 A t f _94252 _94253).
Proof. exact (@lem7062634 (term96 A _94252 t) (term439 A f _94252 _94253)). Qed.
Lemma lem7062637 (a : Prop) : (term503 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7062638 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) : (term418 A _94252 t) = (_94252 = t).
Proof. exact (@lem7062637 (_94252 = t)). Qed.
Lemma lem7062639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7062640 {A : Type'} (_94252 : A -> Prop) (t : A -> Prop) : (term524 A _94252 t) = (term525 A _94252 t).
Proof. exact (MK_COMB (@lem7062639) (@lem7062638 A _94252 t)). Qed.
Lemma lem7062642 (a : Prop) (b : Prop) : (term498 a b) = (term499 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7062643 {A : Type'} (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term553 A f _94252 _94253) = (term554 A f _94252 _94253).
Proof. exact (@lem7062642 (term234 A _94253 f) (_94252 = _94253)). Qed.
Lemma lem7062645 (a : Prop) : (term503 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7062646 {A : Type'} (_94253 : A -> Prop) (f : type686 A) : (term509 A _94253 f) = (@IN (A -> Prop) _94253 f).
Proof. exact (@lem7062645 (@IN (A -> Prop) _94253 f)). Qed.
Lemma lem7062647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7062648 {A : Type'} (_94253 : A -> Prop) (f : type686 A) : (term555 A _94253 f) = (term556 A _94253 f).
Proof. exact (MK_COMB (@lem7062647) (@lem7062646 A _94253 f)). Qed.
Lemma lem7062649 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) : (term96 A _94252 _94253) = (term96 A _94252 _94253).
Proof. exact (eq_refl (term96 A _94252 _94253)). Qed.
Lemma lem7062650 {A : Type'} (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term554 A f _94252 _94253) = (term214 A f _94252 _94253).
Proof. exact (MK_COMB (@lem7062648 A _94253 f) (@lem7062649 A _94252 _94253)). Qed.
Lemma lem7062651 {A : Type'} (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term553 A f _94252 _94253) = (term214 A f _94252 _94253).
Proof. exact (TRANS (@lem7062643 A f _94252 _94253) (@lem7062650 A f _94252 _94253)). Qed.
Lemma lem7062652 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term552 A t f _94252 _94253) = (term557 A t f _94252 _94253).
Proof. exact (MK_COMB (@lem7062640 A _94252 t) (@lem7062651 A f _94252 _94253)). Qed.
Lemma lem7062653 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term551 A t f _94252 _94253) = (term557 A t f _94252 _94253).
Proof. exact (TRANS (@lem7062635 A t f _94252 _94253) (@lem7062652 A t f _94252 _94253)). Qed.
Lemma lem7062654 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7062655 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term558 A t f _94252 _94253) = (term559 A t f _94252 _94253).
Proof. exact (MK_COMB (@lem7062654) (@lem7062653 A t f _94252 _94253)). Qed.
Lemma lem7062656 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) : ((@INTER A _94252 _94253) = (@EMPTY A)) = ((@INTER A _94252 _94253) = (@EMPTY A)).
Proof. exact (eq_refl ((@INTER A _94252 _94253) = (@EMPTY A))). Qed.
Lemma lem7062657 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term550 A t f _94252 _94253) = (term560 A t f _94252 _94253).
Proof. exact (MK_COMB (@lem7062655 A t f _94252 _94253) (@lem7062656 A _94252 _94253)). Qed.
Lemma lem7062658 {A : Type'} (t : A -> Prop) (f : type686 A) (_94252 : A -> Prop) (_94253 : A -> Prop) : (term547 A t f _94252 _94253) = (term560 A t f _94252 _94253).
Proof. exact (TRANS (@lem7062632 A t f _94252 _94253) (@lem7062657 A t f _94252 _94253)). Qed.
Lemma lem7062660 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term214 A f t x.
Proof. exact (conj (@lem7062296 A f t x t' h2) (@lem7062403 A f t x t' h1 h2)). Qed.
Lemma lem7062661 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term234 A t f) (h2 : term410 A f t x t') : term561 A f t x.
Proof. exact (conj (@lem7062289 A t) (@lem7062660 A f t x t' h1 h2)). Qed.
Lemma lem7062663 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term560 A t f _94252 _94253.
Proof. exact (EQ_MP (@lem7062658 A t f _94252 _94253) (@lem7062629 A _94252 _94253 t f h1)). Qed.
Lemma lem7062664 {A : Type'} (_94252 : A -> Prop) (_94253 : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term560 A t f _94252 _94253.
Proof. exact (@lem7062663 A _94252 _94253 t f h1). Qed.
Lemma lem7062665 {A : Type'} (x : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) : term562 A f t x.
Proof. exact (@lem7062664 A t x t f h1). Qed.
Lemma lem7062668 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : (@INTER A t x) = (@EMPTY A).
Proof. exact (@lem7062665 A x t f h1 (@lem7062661 A f t x t' h2 h3)). Qed.
Lemma lem7062669 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : term563 A t x.
Proof. exact (fun h0 : term476 A t x => @lem7062668 A f t x t' h1 h2 h3). Qed.
Lemma lem7062671 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7062672 {A : Type'} (t : A -> Prop) (x : A -> Prop) : (term563 A t x) = ((@INTER A t x) = (@EMPTY A)).
Proof. exact (@lem7062671 ((@INTER A t x) = (@EMPTY A))). Qed.
Lemma lem7062673 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : (@INTER A t x) = (@EMPTY A).
Proof. exact (EQ_MP (@lem7062672 A t x) (@lem7062669 A f t x t' h1 h2 h3)). Qed.
Lemma lem7062676 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7062678 {A : Type'} (t : A -> Prop) (x : A -> Prop) : (term476 A t x) = (term564 A t x).
Proof. exact (@lem7062676 ((@INTER A t x) = (@EMPTY A))). Qed.
Lemma lem7062681 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term410 A f t x t') : term564 A t x.
Proof. exact (EQ_MP (@lem7062678 A t x) (@lem7062120 A f t x t' h1)). Qed.
Lemma lem7062684 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : False.
Proof. exact (@lem7062681 A f t x t' h3 (@lem7062673 A f t x t' h1 h2 h3)). Qed.
Lemma lem7062685 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : term565.
Proof. exact (fun h0 : ~ False => @lem7062684 A f t x t' h1 h2 h3). Qed.
Lemma lem7062687 (p : Prop) : (term490 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7062688 : term565 = False.
Proof. exact (@lem7062687 False). Qed.
Lemma lem7062689 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : False.
Proof. exact (EQ_MP (@lem7062688) (@lem7062685 A f t x t' h1 h2 h3)). Qed.
Lemma lem7062690 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : (term234 A t f) = False.
Proof. exact (prop_ext (fun h4 : term234 A t f => @lem7062689 A f t x t' h1 h2 h3) (fun h4 : False => @lem7062093 A t f h2)). Qed.
Lemma lem7062692 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : False.
Proof. exact (EQ_MP (@lem7062690 A f t x t' h1 h2 h3) (@lem7062093 A t f h2)). Qed.
Lemma lem7062693 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : (term234 A t f) = False.
Proof. exact (prop_ext (fun h4 : term234 A t f => @lem7062692 A f t x t' h1 h2 h3) (fun h4 : False => @lem7061973 A t f h2)). Qed.
Lemma lem7062694 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : False.
Proof. exact (EQ_MP (@lem7062693 A f t x t' h1 h2 h3) (@lem7061973 A t f h2)). Qed.
Lemma lem7062695 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : (term234 A t f) = False.
Proof. exact (prop_ext (fun h4 : term234 A t f => @lem7062694 A f t x t' h1 h2 h3) (fun h4 : False => @lem7061938 A t f h2)). Qed.
Lemma lem7062696 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : False.
Proof. exact (EQ_MP (@lem7062695 A f t x t' h1 h2 h3) (@lem7061938 A t f h2)). Qed.
Lemma lem7062697 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : (term234 A t f) = False.
Proof. exact (prop_ext (fun h4 : term234 A t f => @lem7062696 A f t x t' h1 h2 h3) (fun h4 : False => @lem7061938 A t f h2)). Qed.
Lemma lem7062698 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : False.
Proof. exact (EQ_MP (@lem7062697 A f t x t' h1 h2 h3) (@lem7061938 A t f h2)). Qed.
Lemma lem7062699 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : (term410 A f t x t') = False.
Proof. exact (prop_ext (fun h4 : term410 A f t x t' => @lem7062698 A f t x t' h1 h2 h3) (fun h4 : False => @lem7061829 A f t x t' h3)). Qed.
Lemma lem7062700 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : False.
Proof. exact (EQ_MP (@lem7062699 A f t x t' h1 h2 h3) (@lem7061829 A f t x t' h3)). Qed.
Lemma lem7062701 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : (term234 A t f) = False.
Proof. exact (prop_ext (fun h4 : term234 A t f => @lem7062700 A f t x t' h1 h2 h3) (fun h4 : False => @lem7061797 A t f h2)). Qed.
Lemma lem7062702 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A -> Prop) (t' : A -> Prop) (h1 : term143 A t f) (h2 : term234 A t f) (h3 : term410 A f t x t') : False.
Proof. exact (EQ_MP (@lem7062701 A f t x t' h1 h2 h3) (@lem7061797 A t f h2)). Qed.
Lemma lem7062703 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term413 A f t t') (h3 : term234 A t f) : False.
Proof. exact (ex_elim (@lem7061697 A f t t' h2) (fun x : A -> Prop => fun h0 : term412 A f t t' x => @lem7062702 A f t x t' h1 h3 h0)). Qed.
Lemma lem7062704 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term357 A f t) (h3 : term234 A t f) : False.
Proof. exact (ex_elim (@lem7061535 A f t h2) (fun t' : A -> Prop => fun h0 : term414 A f t t' => @lem7062703 A t' t f h1 h0 h3)). Qed.
Lemma lem7062705 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term357 A f t) (h3 : term234 A t f) : (term234 A t f) = False.
Proof. exact (prop_ext (fun h4 : term234 A t f => @lem7062704 A t f h1 h2 h3) (fun h4 : False => @lem7061690 A t f h3)). Qed.
Lemma lem7062706 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term357 A f t) (h3 : term234 A t f) : False.
Proof. exact (EQ_MP (@lem7062705 A t f h1 h2 h3) (@lem7061690 A t f h3)). Qed.
Lemma lem7062707 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term357 A f t) (h3 : term234 A t f) : term362 A f.
Proof. exact (fun h0 : @FINITE (A -> Prop) f => @lem7062706 A t f h1 h2 h3). Qed.
Lemma lem7062708 {A : Type'} (f : type686 A) : (term362 A f) = (term363 A f).
Proof. exact (@lem69 (@FINITE (A -> Prop) f)). Qed.
Lemma lem7062709 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term357 A f t) (h3 : term234 A t f) : term363 A f.
Proof. exact (EQ_MP (@lem7062708 A f) (@lem7062707 A t f h1 h2 h3)). Qed.
Lemma lem7062710 {A : Type'} (f : type686 A) (t : A -> Prop) (h1 : term143 A t f) (h2 : term357 A f t) : term366 A t f.
Proof. exact (fun h0 : term234 A t f => @lem7062709 A t f h1 h2 h0). Qed.
Lemma lem7062711 {A : Type'} (f : type686 A) (t : A -> Prop) (h1 : term357 A f t) : term369 A t f.
Proof. exact (fun h0 : term143 A t f => @lem7062710 A f t h0 h1). Qed.
Lemma lem7062712 {A : Type'} (f : type686 A) (t : A -> Prop) (h1 : term357 A f t) : term372 A t f.
Proof. exact (fun h0 : term123 A t f => @lem7062711 A f t h1). Qed.
Lemma lem7062713 {A : Type'} (t : A -> Prop) (f : type686 A) : term374 A t f.
Proof. exact (fun h0 : term357 A f t => @lem7062712 A f t h0). Qed.
Lemma lem7062718 {A : Type'} (f : type686 A) : term378 A f.
Proof. exact (fun t : A -> Prop => @lem7062713 A t f). Qed.
Lemma lem7062723 {A : Type'} : term382 A.
Proof. exact (fun f : type686 A => @lem7062718 A f). Qed.
Lemma lem7062724 {A : Type'} : term381 A.
Proof. exact (EQ_MP (@lem7061379 A) (@lem7062723 A)). Qed.
Lemma lem7062725 {A : Type'} (f : type686 A) : term566 A f.
Proof. exact (@lem7062724 A f). Qed.
Lemma lem7062726 {A : Type'} (f : type686 A) : (term566 A f) = (term377 A f).
Proof. exact (eq_refl (term566 A f)). Qed.
Lemma lem7062727 {A : Type'} (f : type686 A) : term377 A f.
Proof. exact (EQ_MP (@lem7062726 A f) (@lem7062725 A f)). Qed.
Lemma lem7062728 {A : Type'} (f : type686 A) (t : A -> Prop) : term567 A f t.
Proof. exact (@lem7062727 A f t). Qed.
Lemma lem7062729 {A : Type'} (t : A -> Prop) (f : type686 A) : (term567 A f t) = (term358 A t f).
Proof. exact (eq_refl (term567 A f t)). Qed.
Lemma lem7062730 {A : Type'} (t : A -> Prop) (f : type686 A) : term358 A t f.
Proof. exact (EQ_MP (@lem7062729 A t f) (@lem7062728 A f t)). Qed.
Lemma lem7062732 {A : Type'} (t : A -> Prop) (f : type686 A) : term358 A t f.
Proof. exact (@lem7061090 A t f (@lem7062730 A t f)). Qed.
Lemma lem7062733 {A : Type'} (f : type686 A) (t : A -> Prop) (h1 : term357 A f t) : term371 A t f.
Proof. exact (@lem7062732 A t f (@lem7061074 A f t h1)). Qed.
Lemma lem7062734 {A : Type'} (f : type686 A) (t : A -> Prop) (h1 : term123 A t f) (h2 : term357 A f t) : term368 A t f.
Proof. exact (@lem7062733 A f t h2 (@lem7059747 A t f h1)). Qed.
Lemma lem7062735 {A : Type'} (f : type686 A) (t : A -> Prop) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term357 A f t) : term365 A t f.
Proof. exact (@lem7062734 A f t h2 h3 (@lem7059746 A t f h1)). Qed.
Lemma lem7062736 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term357 A f t) (h4 : term234 A t f) : term362 A f.
Proof. exact (@lem7062735 A f t h1 h2 h3 (@lem7060400 A t f h4)). Qed.
Lemma lem7062737 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : False.
Proof. exact (@lem7062736 A t f h1 h2 h4 h5 (@lem7060399 A f h3)). Qed.
Lemma lem7062738 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : (@FINITE (A -> Prop) f) = False.
Proof. exact (prop_ext (fun h6 : @FINITE (A -> Prop) f => @lem7062737 A t f h1 h2 h3 h4 h5) (fun h6 : False => @lem7060399 A f h3)). Qed.
Lemma lem7062739 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : False.
Proof. exact (EQ_MP (@lem7062738 A t f h1 h2 h3 h4 h5) (@lem7060399 A f h3)). Qed.
Lemma lem7062740 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : (term234 A t f) = False.
Proof. exact (prop_ext (fun h6 : term234 A t f => @lem7062739 A t f h1 h2 h3 h4 h5) (fun h6 : False => @lem7060400 A t f h5)). Qed.
Lemma lem7062741 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : False.
Proof. exact (EQ_MP (@lem7062740 A t f h1 h2 h3 h4 h5) (@lem7060400 A t f h5)). Qed.
Lemma lem7062742 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : (term143 A t f) = False.
Proof. exact (prop_ext (fun h6 : term143 A t f => @lem7062741 A t f h1 h2 h3 h4 h5) (fun h6 : False => @lem7059746 A t f h1)). Qed.
Lemma lem7062743 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : False.
Proof. exact (EQ_MP (@lem7062742 A t f h1 h2 h3 h4 h5) (@lem7059746 A t f h1)). Qed.
Lemma lem7062744 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : (term123 A t f) = False.
Proof. exact (prop_ext (fun h6 : term123 A t f => @lem7062743 A t f h1 h2 h3 h4 h5) (fun h6 : False => @lem7059747 A t f h2)). Qed.
Lemma lem7062745 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : False.
Proof. exact (EQ_MP (@lem7062744 A t f h1 h2 h3 h4 h5) (@lem7059747 A t f h2)). Qed.
Lemma lem7062746 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : (term357 A f t) = False.
Proof. exact (prop_ext (fun h6 : term357 A f t => @lem7062745 A t f h1 h2 h3 h4 h5) (fun h6 : False => @lem7061074 A f t h4)). Qed.
Lemma lem7062747 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term357 A f t) (h5 : term234 A t f) : False.
Proof. exact (EQ_MP (@lem7062746 A t f h1 h2 h3 h4 h5) (@lem7061074 A f t h4)). Qed.
Lemma lem7062748 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term234 A t f) : term356 A f t.
Proof. exact (fun h0 : term357 A f t => @lem7062747 A t f h1 h2 h3 h0 h4). Qed.
Lemma lem7062749 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term234 A t f) : term347 A f t.
Proof. exact (EQ_MP (@lem7061073 A f t) (@lem7062748 A t f h1 h2 h3 h4)). Qed.
Lemma lem7062750 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term234 A t f) : (term276 A f t) = (@EMPTY A).
Proof. exact (EQ_MP (@lem7061059 A f t) (@lem7062749 A t f h1 h2 h3 h4)). Qed.
Lemma lem7062751 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term234 A t f) : term299 A t f.
Proof. exact (EQ_MP (@lem7060966 A t f h2 h3 h4) (@lem7062750 A t f h1 h2 h3 h4)). Qed.
Lemma lem7062752 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term234 A t f) : (term267 A t f) = (term151 A t f).
Proof. exact (@lem7060410 A t f (@lem7062751 A t f h1 h2 h3 h4)). Qed.
Lemma lem7062753 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term234 A t f) : (term151 A t f) = (term267 A t f).
Proof. exact (EQ_MP (@lem7060406 A t f) (@lem7062752 A t f h1 h2 h3 h4)). Qed.
Lemma lem7062754 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : term59 A t f.
Proof. exact (proj2 (@lem7060382 A t f h1)). Qed.
Lemma lem7062755 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term231 A t f) : (term43 A f) = (@nsum (A -> Prop) f (@CARD A)).
Proof. exact (proj1 (@lem7060382 A t f h1)). Qed.
Lemma lem7062756 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term59 A t f) : @FINITE (A -> Prop) f.
Proof. exact (proj2 (@lem7060383 A t f h1)). Qed.
Lemma lem7062757 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term59 A t f) : term234 A t f.
Proof. exact (proj1 (@lem7060383 A t f h1)). Qed.
Lemma lem7062758 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term234 A t f) : (@FINITE (A -> Prop) f) = ((term151 A t f) = (term267 A t f)).
Proof. exact (prop_ext (fun h5 : @FINITE (A -> Prop) f => @lem7062753 A t f h1 h2 h3 h4) (fun h5 : (term151 A t f) = (term267 A t f) => @lem7060399 A f h3)). Qed.
Lemma lem7062759 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term234 A t f) : (term151 A t f) = (term267 A t f).
Proof. exact (EQ_MP (@lem7062758 A t f h1 h2 h3 h4) (@lem7060399 A f h3)). Qed.
Lemma lem7062760 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term234 A t f) : (term234 A t f) = ((term151 A t f) = (term267 A t f)).
Proof. exact (prop_ext (fun h5 : term234 A t f => @lem7062759 A t f h1 h2 h3 h4) (fun h5 : (term151 A t f) = (term267 A t f) => @lem7060400 A t f h4)). Qed.
Lemma lem7062761 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : @FINITE (A -> Prop) f) (h4 : term234 A t f) : (term151 A t f) = (term267 A t f).
Proof. exact (EQ_MP (@lem7062760 A t f h1 h2 h3 h4) (@lem7060400 A t f h4)). Qed.
Lemma lem7062762 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term234 A t f) (h4 : term59 A t f) : (@FINITE (A -> Prop) f) = ((term151 A t f) = (term267 A t f)).
Proof. exact (prop_ext (fun h5 : @FINITE (A -> Prop) f => @lem7062761 A t f h1 h2 h5 h3) (fun h5 : (term151 A t f) = (term267 A t f) => @lem7062756 A t f h4)). Qed.
Lemma lem7062763 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term234 A t f) (h4 : term59 A t f) : (term151 A t f) = (term267 A t f).
Proof. exact (EQ_MP (@lem7062762 A t f h1 h2 h3 h4) (@lem7062756 A t f h4)). Qed.
Lemma lem7062764 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term59 A t f) : (term234 A t f) = ((term151 A t f) = (term267 A t f)).
Proof. exact (prop_ext (fun h4 : term234 A t f => @lem7062763 A t f h1 h2 h4 h3) (fun h4 : (term151 A t f) = (term267 A t f) => @lem7062757 A t f h3)). Qed.
Lemma lem7062765 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term59 A t f) : (term151 A t f) = (term267 A t f).
Proof. exact (EQ_MP (@lem7062764 A t f h1 h2 h3) (@lem7062757 A t f h3)). Qed.
Lemma lem7062766 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term59 A t f) (h4 : (term43 A f) = (@nsum (A -> Prop) f (@CARD A))) : (term151 A t f) = (term245 A t f).
Proof. exact (EQ_MP (@lem7060398 A t f h4) (@lem7062765 A t f h1 h2 h3)). Qed.
Lemma lem7062767 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term231 A t f) (h4 : (term43 A f) = (@nsum (A -> Prop) f (@CARD A))) : (term59 A t f) = ((term151 A t f) = (term245 A t f)).
Proof. exact (prop_ext (fun h5 : term59 A t f => @lem7062766 A t f h1 h2 h5 h4) (fun h5 : (term151 A t f) = (term245 A t f) => @lem7062754 A t f h3)). Qed.
Lemma lem7062768 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term231 A t f) (h4 : (term43 A f) = (@nsum (A -> Prop) f (@CARD A))) : (term151 A t f) = (term245 A t f).
Proof. exact (EQ_MP (@lem7062767 A t f h1 h2 h3 h4) (@lem7062754 A t f h3)). Qed.
Lemma lem7062769 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term231 A t f) : ((term43 A f) = (@nsum (A -> Prop) f (@CARD A))) = ((term151 A t f) = (term245 A t f)).
Proof. exact (prop_ext (fun h4 : (term43 A f) = (@nsum (A -> Prop) f (@CARD A)) => @lem7062768 A t f h1 h2 h3 h4) (fun h4 : (term151 A t f) = (term245 A t f) => @lem7062755 A t f h3)). Qed.
Lemma lem7062770 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term231 A t f) : (term151 A t f) = (term245 A t f).
Proof. exact (EQ_MP (@lem7062769 A t f h1 h2 h3) (@lem7062755 A t f h3)). Qed.
Lemma lem7062771 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : term263 A t f.
Proof. exact (fun h0 : term231 A t f => @lem7062770 A t f h1 h2 h0). Qed.
Lemma lem7062772 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) : term262 A t f.
Proof. exact (EQ_MP (@lem7060381 A t f h1 h2) (@lem7062771 A t f h1 h2)). Qed.
Lemma lem7062773 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term61 A t f) : (term151 A t f) = (term154 A t f).
Proof. exact (@lem7062772 A t f h1 h2 (@lem7059744 A t f h3)). Qed.
Lemma lem7062774 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term145 A t f) : term143 A t f.
Proof. exact (proj2 (@lem7059745 A t f h1)). Qed.
Lemma lem7062775 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term145 A t f) : term123 A t f.
Proof. exact (proj1 (@lem7059745 A t f h1)). Qed.
Lemma lem7062776 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term61 A t f) : (term143 A t f) = ((term151 A t f) = (term154 A t f)).
Proof. exact (prop_ext (fun h4 : term143 A t f => @lem7062773 A t f h1 h2 h3) (fun h4 : (term151 A t f) = (term154 A t f) => @lem7059746 A t f h1)). Qed.
Lemma lem7062777 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term61 A t f) : (term151 A t f) = (term154 A t f).
Proof. exact (EQ_MP (@lem7062776 A t f h1 h2 h3) (@lem7059746 A t f h1)). Qed.
Lemma lem7062778 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term61 A t f) : (term123 A t f) = ((term151 A t f) = (term154 A t f)).
Proof. exact (prop_ext (fun h4 : term123 A t f => @lem7062777 A t f h1 h2 h3) (fun h4 : (term151 A t f) = (term154 A t f) => @lem7059747 A t f h2)). Qed.
Lemma lem7062779 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term143 A t f) (h2 : term123 A t f) (h3 : term61 A t f) : (term151 A t f) = (term154 A t f).
Proof. exact (EQ_MP (@lem7062778 A t f h1 h2 h3) (@lem7059747 A t f h2)). Qed.
Lemma lem7062780 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : term145 A t f) (h3 : term61 A t f) : (term143 A t f) = ((term151 A t f) = (term154 A t f)).
Proof. exact (prop_ext (fun h4 : term143 A t f => @lem7062779 A t f h4 h1 h3) (fun h4 : (term151 A t f) = (term154 A t f) => @lem7062774 A t f h2)). Qed.
Lemma lem7062781 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term123 A t f) (h2 : term145 A t f) (h3 : term61 A t f) : (term151 A t f) = (term154 A t f).
Proof. exact (EQ_MP (@lem7062780 A t f h1 h2 h3) (@lem7062774 A t f h2)). Qed.
Lemma lem7062782 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term145 A t f) (h2 : term61 A t f) : (term123 A t f) = ((term151 A t f) = (term154 A t f)).
Proof. exact (prop_ext (fun h3 : term123 A t f => @lem7062781 A t f h3 h1 h2) (fun h3 : (term151 A t f) = (term154 A t f) => @lem7062775 A t f h1)). Qed.
Lemma lem7062783 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term145 A t f) (h2 : term61 A t f) : (term151 A t f) = (term154 A t f).
Proof. exact (EQ_MP (@lem7062782 A t f h1 h2) (@lem7062775 A t f h1)). Qed.
Lemma lem7062784 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : term61 A t f) : term155 A t f.
Proof. exact (fun h0 : term145 A t f => @lem7062783 A t f h0 h1). Qed.
Lemma lem7062785 {A : Type'} (t : A -> Prop) (f : type686 A) : term156 A t f.
Proof. exact (fun h0 : term61 A t f => @lem7062784 A t f h0). Qed.
Lemma lem7062790 {A : Type'} (t : A -> Prop) : term158 A t.
Proof. exact (fun f : type686 A => @lem7062785 A t f). Qed.
Lemma lem7062795 {A : Type'} : term160 A.
Proof. exact (fun t : A -> Prop => @lem7062790 A t). Qed.
Lemma lem7062796 {A : Type'} : term161 A.
Proof. exact (EQ_MP (@lem7059743 A) (@lem7062795 A)). Qed.
Lemma lem7062797 {A : Type'} : term77 A.
Proof. exact (EQ_MP (@lem7059544 A) (@lem7062796 A)). Qed.
Lemma lem7062798 {A : Type'} : term47 A.
Proof. exact (@lem7059230 A (@lem7062797 A)). Qed.
Lemma lem7062799 {A : Type'} : term46 A.
Proof. exact (EQ_MP (@lem7059197 A) (@lem7062798 A)). Qed.
