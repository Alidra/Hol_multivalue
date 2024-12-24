Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318142_term_abbrevs.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_LE_WELLDEF_spec.
Require Import thm1317744_spec.
Require Import thm23443_spec.
Require Import thm32_spec.
Lemma lem1318037 : hreal_le = term0.
Proof. exact (@hreal_le_def). Qed.
Lemma lem1318038 (x : hreal) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1318039 (x : hreal) : (hreal_le x) = (term1 x).
Proof. exact (MK_COMB (@lem1318037) (@lem1318038 x)). Qed.
Lemma lem1318040 (x : hreal) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1318041 (x : hreal) : (term3 x) = (term3 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1318042 (x : hreal) : ((hreal_le x) = (term1 x)) = ((hreal_le x) = (term2 x)).
Proof. exact (MK_COMB (@lem1318041 x) (@lem1318040 x)). Qed.
Lemma lem1318043 (x : hreal) : (hreal_le x) = (term2 x).
Proof. exact (EQ_MP (@lem1318042 x) (@lem1318039 x)). Qed.
Lemma lem1318044 (y : hreal) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1318045 (x : hreal) (y : hreal) : (hreal_le x y) = (term4 x y).
Proof. exact (MK_COMB (@lem1318043 x) (@lem1318044 y)). Qed.
Lemma lem1318046 (x : hreal) (y : hreal) : (term4 x y) = (term5 x y).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1318047 (x : hreal) (y : hreal) : (term6 x y) = (term6 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1318048 (x : hreal) (y : hreal) : ((hreal_le x y) = (term4 x y)) = ((hreal_le x y) = (term5 x y)).
Proof. exact (MK_COMB (@lem1318047 x y) (@lem1318046 x y)). Qed.
Lemma lem1318049 (x : hreal) (y : hreal) : (hreal_le x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1318048 x y) (@lem1318045 x y)). Qed.
Lemma lem1318050 (x : nadd) : (term7 x) = ((term8 x) = (nadd_eq x)).
Proof. exact (@lem1317744 (nadd_eq x)). Qed.
Lemma lem1318051 (x : nadd) : (nadd_eq x) = (nadd_eq x).
Proof. exact (eq_refl (nadd_eq x)). Qed.
Lemma lem1318052 (x : nadd) : term7 x.
Proof. exact (ex_intro (term9 x) x (@lem1318051 x)). Qed.
Lemma lem1318053 (x : nadd) : (term8 x) = (nadd_eq x).
Proof. exact (EQ_MP (@lem1318050 x) (@lem1318052 x)). Qed.
Lemma lem1318054 (x : nadd) (y : nadd) : (term10 x y) = (term11 x y).
Proof. exact (@lem1318049 (term12 x) (term12 y)). Qed.
Lemma lem1318055 (x : nadd) : (term8 x) = (nadd_eq x).
Proof. exact (@lem1318053 x). Qed.
Lemma lem1318056 (y : nadd) : (term8 y) = (nadd_eq y).
Proof. exact (@lem1318053 y). Qed.
Lemma lem1318057 (x : nadd) (y : nadd) : (term13 x y) = (term13 x y).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1318058 (y : nadd) (x : nadd) : (term14 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1318057 x y) (@lem1318055 x)). Qed.
Lemma lem1318059 (y : nadd) (x : nadd) : (term15 y x) = (term16 y x).
Proof. exact (eq_refl (term15 y x)). Qed.
Lemma lem1318060 (y : nadd) (x : nadd) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1318061 (y : nadd) (x : nadd) : ((term14 y x) = (term15 y x)) = ((term14 y x) = (term16 y x)).
Proof. exact (MK_COMB (@lem1318060 y x) (@lem1318059 y x)). Qed.
Lemma lem1318062 (y : nadd) (x : nadd) : (term14 y x) = (term18 y x).
Proof. exact (eq_refl (term14 y x)). Qed.
Lemma lem1318063 : (@eq ((nadd -> Prop) -> Prop)) = (@eq ((nadd -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((nadd -> Prop) -> Prop))). Qed.
Lemma lem1318064 (y : nadd) (x : nadd) : (term17 y x) = (term19 y x).
Proof. exact (MK_COMB (@lem1318063) (@lem1318062 y x)). Qed.
Lemma lem1318065 (y : nadd) (x : nadd) : (term16 y x) = (term16 y x).
Proof. exact (eq_refl (term16 y x)). Qed.
Lemma lem1318066 (y : nadd) (x : nadd) : ((term14 y x) = (term16 y x)) = ((term18 y x) = (term16 y x)).
Proof. exact (MK_COMB (@lem1318064 y x) (@lem1318065 y x)). Qed.
Lemma lem1318067 (y : nadd) (x : nadd) : ((term14 y x) = (term15 y x)) = ((term18 y x) = (term16 y x)).
Proof. exact (TRANS (@lem1318061 y x) (@lem1318066 y x)). Qed.
Lemma lem1318068 (y : nadd) (x : nadd) : (term18 y x) = (term16 y x).
Proof. exact (EQ_MP (@lem1318067 y x) (@lem1318058 y x)). Qed.
Lemma lem1318069 (x : nadd) (y : nadd) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1318068 y x) (@lem1318056 y)). Qed.
Lemma lem1318070 (x : nadd) (y : nadd) : (term21 x y) = ((term10 x y) = (term22 x y)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1318071 (x : nadd) (y : nadd) : (term23 x y) = (term23 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1318072 (x : nadd) (y : nadd) : ((term20 x y) = (term21 x y)) = ((term20 x y) = ((term10 x y) = (term22 x y))).
Proof. exact (MK_COMB (@lem1318071 x y) (@lem1318070 x y)). Qed.
Lemma lem1318073 (x : nadd) (y : nadd) : (term20 x y) = ((term10 x y) = (term11 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1318074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1318075 (x : nadd) (y : nadd) : (term23 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1318074) (@lem1318073 x y)). Qed.
Lemma lem1318076 (x : nadd) (y : nadd) : ((term10 x y) = (term22 x y)) = ((term10 x y) = (term22 x y)).
Proof. exact (eq_refl ((term10 x y) = (term22 x y))). Qed.
Lemma lem1318077 (x : nadd) (y : nadd) : ((term20 x y) = ((term10 x y) = (term22 x y))) = (((term10 x y) = (term11 x y)) = ((term10 x y) = (term22 x y))).
Proof. exact (MK_COMB (@lem1318075 x y) (@lem1318076 x y)). Qed.
Lemma lem1318078 (x : nadd) (y : nadd) : ((term20 x y) = (term21 x y)) = (((term10 x y) = (term11 x y)) = ((term10 x y) = (term22 x y))).
Proof. exact (TRANS (@lem1318072 x y) (@lem1318077 x y)). Qed.
Lemma lem1318079 (x : nadd) (y : nadd) : ((term10 x y) = (term11 x y)) = ((term10 x y) = (term22 x y)).
Proof. exact (EQ_MP (@lem1318078 x y) (@lem1318069 x y)). Qed.
Lemma lem1318080 (x : nadd) (y : nadd) : (term10 x y) = (term22 x y).
Proof. exact (EQ_MP (@lem1318079 x y) (@lem1318054 x y)). Qed.
Lemma lem1318081 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term25 u x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1318082 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term26 x x' y y'.
Proof. exact (proj2 (@lem1318081 u x x' y y' h1)). Qed.
Lemma lem1318083 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : (nadd_le x' y') = u.
Proof. exact (proj1 (@lem1318081 u x x' y y' h1)). Qed.
Lemma lem1318084 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : nadd_eq y y'.
Proof. exact (proj2 (@lem1318082 u x x' y y' h1)). Qed.
Lemma lem1318085 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : nadd_eq x x'.
Proof. exact (proj1 (@lem1318082 u x x' y y' h1)). Qed.
Lemma lem1318086 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term26 x x' y y'.
Proof. exact (conj (@lem1318085 u x x' y y' h1) (@lem1318084 u x x' y y' h1)). Qed.
Lemma lem1318087 (x : nadd) : term27 x.
Proof. exact (@lem1270569 x). Qed.
Lemma lem1318088 (x : nadd) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1318089 (x : nadd) : term28 x.
Proof. exact (EQ_MP (@lem1318088 x) (@lem1318087 x)). Qed.
Lemma lem1318090 (x : nadd) (x' : nadd) : term29 x x'.
Proof. exact (@lem1318089 x x'). Qed.
Lemma lem1318091 (x : nadd) (x' : nadd) : (term29 x x') = (term30 x x').
Proof. exact (eq_refl (term29 x x')). Qed.
Lemma lem1318092 (x : nadd) (x' : nadd) : term30 x x'.
Proof. exact (EQ_MP (@lem1318091 x x') (@lem1318090 x x')). Qed.
Lemma lem1318093 (x : nadd) (x' : nadd) (y : nadd) : term31 x x' y.
Proof. exact (@lem1318092 x x' y). Qed.
Lemma lem1318094 (x : nadd) (y : nadd) (x' : nadd) : (term31 x x' y) = (term32 x y x').
Proof. exact (eq_refl (term31 x x' y)). Qed.
Lemma lem1318095 (x : nadd) (y : nadd) (x' : nadd) : term32 x y x'.
Proof. exact (EQ_MP (@lem1318094 x y x') (@lem1318093 x x' y)). Qed.
Lemma lem1318096 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term33 x y x' y'.
Proof. exact (@lem1318095 x y x' y'). Qed.
Lemma lem1318097 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term33 x y x' y') = (term34 x y x' y').
Proof. exact (eq_refl (term33 x y x' y')). Qed.
Lemma lem1318100 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term34 x y x' y'.
Proof. exact (EQ_MP (@lem1318097 x y x' y') (@lem1318096 x y x' y')). Qed.
Lemma lem1318101 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : (nadd_le x y) = (nadd_le x' y').
Proof. exact (@lem1318100 x y x' y' (@lem1318086 u x x' y y' h1)). Qed.
Lemma lem1318102 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : (nadd_le x y) = u.
Proof. exact (TRANS (@lem1318101 u x x' y y' h1) (@lem1318083 u x x' y y' h1)). Qed.
Lemma lem1318103 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (h1 : term35 u x x' y) : term35 u x x' y.
Proof. exact (h1). Qed.
Lemma lem1318104 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (h1 : term35 u x x' y) : (nadd_le x y) = u.
Proof. exact (ex_elim (@lem1318103 u x x' y h1) (fun y' : nadd => fun h0 : term36 u x x' y y' => @lem1318102 u x x' y y' h0)). Qed.
Lemma lem1318105 (u : Prop) (x : nadd) (y : nadd) (h1 : term37 u x y) : term37 u x y.
Proof. exact (h1). Qed.
Lemma lem1318106 (u : Prop) (x : nadd) (y : nadd) (h1 : term37 u x y) : (nadd_le x y) = u.
Proof. exact (ex_elim (@lem1318105 u x y h1) (fun x' : nadd => fun h0 : term38 u x y x' => @lem1318104 u x x' y h0)). Qed.
Lemma lem1318107 (x : nadd) (y : nadd) (u : Prop) (h1 : (nadd_le x y) = u) : (nadd_le x y) = u.
Proof. exact (h1). Qed.
Lemma lem1318108 (x : nadd) : term39 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1318109 (x : nadd) : (term39 x) = (nadd_eq x x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1318110 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1318109 x) (@lem1318108 x)). Qed.
Lemma lem1318111 (y : nadd) : term39 y.
Proof. exact (@lem1267990 y). Qed.
Lemma lem1318112 (y : nadd) : (term39 y) = (nadd_eq y y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1318113 (y : nadd) : nadd_eq y y.
Proof. exact (EQ_MP (@lem1318112 y) (@lem1318111 y)). Qed.
Lemma lem1318114 (x : nadd) (y : nadd) : term40 x y.
Proof. exact (conj (@lem1318110 x) (@lem1318113 y)). Qed.
Lemma lem1318115 (x : nadd) (y : nadd) (u : Prop) (h1 : (nadd_le x y) = u) : term41 u x y.
Proof. exact (conj (@lem1318107 x y u h1) (@lem1318114 x y)). Qed.
Lemma lem1318116 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term25 u x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1318117 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term35 u x x' y.
Proof. exact (ex_intro (term36 u x x' y) y' (@lem1318116 u x x' y y' h1)). Qed.
Lemma lem1318118 (u : Prop) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term37 u x y.
Proof. exact (ex_intro (term38 u x y) x' (@lem1318117 u x x' y y' h1)). Qed.
Lemma lem1318121 (x' : nadd) (y' : nadd) (u : Prop) (x : nadd) (y : nadd) : term42 x' y' u x y.
Proof. exact (fun h0 : term25 u x x' y y' => @lem1318118 u x x' y y' h0). Qed.
Lemma lem1318122 (u : Prop) (x : nadd) (y : nadd) : term43 u x y.
Proof. exact (@lem1318121 x y u x y). Qed.
Lemma lem1318123 (x : nadd) (y : nadd) (u : Prop) (h1 : (nadd_le x y) = u) : term37 u x y.
Proof. exact (@lem1318122 u x y (@lem1318115 x y u h1)). Qed.
Lemma lem1318124 (u : Prop) (x : nadd) (y : nadd) : term44 u x y.
Proof. exact (fun h0 : (nadd_le x y) = u => @lem1318123 x y u h0). Qed.
Lemma lem1318125 (x : nadd) (y : nadd) (u : Prop) : term45 x y u.
Proof. exact (fun h0 : term37 u x y => @lem1318106 u x y h0). Qed.
Lemma lem1318126 (u : Prop) (x : nadd) (y : nadd) : term46 u x y.
Proof. exact (conj (@lem1318125 x y u) (@lem1318124 u x y)). Qed.
Lemma lem1318127 (x : nadd) (y : nadd) (u : Prop) : (term46 u x y) = ((term37 u x y) = ((nadd_le x y) = u)).
Proof. exact (@lem32 (term37 u x y) ((nadd_le x y) = u)). Qed.
Lemma lem1318128 (x : nadd) (y : nadd) (u : Prop) : (term37 u x y) = ((nadd_le x y) = u).
Proof. exact (EQ_MP (@lem1318127 x y u) (@lem1318126 u x y)). Qed.
Lemma lem1318129 (x : nadd) (y : nadd) : (term47 x y) = (term48 x y).
Proof. exact (fun_ext (fun u : Prop => @lem1318128 x y u)). Qed.
Lemma lem1318130 : (@ε Prop) = (@ε Prop).
Proof. exact (eq_refl (@ε Prop)). Qed.
Lemma lem1318131 (x : nadd) (y : nadd) : (term22 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1318130) (@lem1318129 x y)). Qed.
Lemma lem1318132 (x : nadd) (y : nadd) : (term10 x y) = (term49 x y).
Proof. exact (TRANS (@lem1318080 x y) (@lem1318131 x y)). Qed.
Lemma lem1318133 {A : Type'} (x : A) : term50 A x.
Proof. exact (@lem23443 A x). Qed.
Lemma lem1318134 {A : Type'} (x : A) : (term50 A x) = ((term51 A x) = x).
Proof. exact (eq_refl (term50 A x)). Qed.
Lemma lem1318137 {A : Type'} (x : A) : (term51 A x) = x.
Proof. exact (EQ_MP (@lem1318134 A x) (@lem1318133 A x)). Qed.
Lemma lem1318138 (x : Prop) : (term52 x) = x.
Proof. exact (@lem1318137 Prop x). Qed.
Lemma lem1318139 (x : nadd) (y : nadd) : (term49 x y) = (nadd_le x y).
Proof. exact (@lem1318138 (nadd_le x y)). Qed.
Lemma lem1318140 (x : nadd) (y : nadd) : (term53 x y) = (term53 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem1318141 (x : nadd) (y : nadd) : ((term10 x y) = (term49 x y)) = ((term10 x y) = (nadd_le x y)).
Proof. exact (MK_COMB (@lem1318140 x y) (@lem1318139 x y)). Qed.
Lemma lem1318142 (x : nadd) (y : nadd) : (term10 x y) = (nadd_le x y).
Proof. exact (EQ_MP (@lem1318141 x y) (@lem1318132 x y)). Qed.
