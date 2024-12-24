Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_1_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import EXTENSION_spec.
Require Import FINITE_RULES_spec.
Require Import HAS_SIZE_spec.
Require Import IN_SING_spec.
Require Import IN_UNIV_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import one_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm513079_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem7602742 : term0.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem7602743 : term1.
Proof. exact (proj2 (@lem7602742)). Qed.
Lemma lem7602744 : term2.
Proof. exact (proj2 (@lem7602743)). Qed.
Lemma lem7602745 : term3.
Proof. exact (proj2 (@lem7602744)). Qed.
Lemma lem7602746 : term4.
Proof. exact (proj2 (@lem7602745)). Qed.
Lemma lem7602747 : term5.
Proof. exact (proj2 (@lem7602746)). Qed.
Lemma lem7602748 : term6.
Proof. exact (proj2 (@lem7602747)). Qed.
Lemma lem7602749 : term7.
Proof. exact (proj2 (@lem7602748)). Qed.
Lemma lem7602750 : term8.
Proof. exact (proj2 (@lem7602749)). Qed.
Lemma lem7602751 : term9.
Proof. exact (proj2 (@lem7602750)). Qed.
Lemma lem7602752 (m : nat) : term10 m.
Proof. exact (@lem7602751 m). Qed.
Lemma lem7602753 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem7602754 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem7602753 m) (@lem7602752 m)). Qed.
Lemma lem7602755 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem7602754 m n). Qed.
Lemma lem7602756 (m : nat) (n : nat) : (term12 m n) = (((BIT1 m) = (BIT1 n)) = (m = n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem7602796 : term13.
Proof. exact (proj1 (@lem7602742)). Qed.
Lemma lem7602797 (m : nat) : term14 m.
Proof. exact (@lem7602796 m). Qed.
Lemma lem7602798 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem7602799 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem7602798 m) (@lem7602797 m)). Qed.
Lemma lem7602800 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem7602799 m n). Qed.
Lemma lem7602801 (m : nat) (n : nat) : (term16 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem7603034 : term17.
Proof. exact (EQ_MP (@lem513079) (@lem0)). Qed.
Lemma lem7603035 : term18.
Proof. exact (proj2 (@lem7603034)). Qed.
Lemma lem7603046 : term19.
Proof. exact (proj1 (@lem7603034)). Qed.
Lemma lem7603047 (n : nat) : term20 n.
Proof. exact (@lem7603046 n). Qed.
Lemma lem7603048 (n : nat) : (term20 n) = ((term21 n) = (term22 n)).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem7603053 {A : Type'} : term23 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem7603054 {A : Type'} (x : A) : term24 A x.
Proof. exact (@lem7603053 A x). Qed.
Lemma lem7603055 {A : Type'} (x : A) : (term24 A x) = (term25 A x).
Proof. exact (eq_refl (term24 A x)). Qed.
Lemma lem7603056 {A : Type'} (x : A) : term25 A x.
Proof. exact (EQ_MP (@lem7603055 A x) (@lem7603054 A x)). Qed.
Lemma lem7603057 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (@lem7603056 A x s). Qed.
Lemma lem7603058 {A : Type'} (x : A) (s : A -> Prop) : (term26 A x s) = (term27 A x s).
Proof. exact (eq_refl (term26 A x s)). Qed.
Lemma lem7603059 {A : Type'} (x : A) (s : A -> Prop) : term27 A x s.
Proof. exact (EQ_MP (@lem7603058 A x s) (@lem7603057 A x s)). Qed.
Lemma lem7603060 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7603061 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term28 A x s) = (term29 A x s).
Proof. exact (@lem7603059 A x s (@lem7603060 A s h1)). Qed.
Lemma lem7603068 {A : Type'} : term30 A.
Proof. exact (proj2 (@lem3197565 A)). Qed.
Lemma lem7603069 {A : Type'} (x : A) : term31 A x.
Proof. exact (@lem7603068 A x). Qed.
Lemma lem7603070 {A : Type'} (x : A) : (term31 A x) = (term32 A x).
Proof. exact (eq_refl (term31 A x)). Qed.
Lemma lem7603071 {A : Type'} (x : A) : term32 A x.
Proof. exact (EQ_MP (@lem7603070 A x) (@lem7603069 A x)). Qed.
Lemma lem7603072 {A : Type'} (x : A) (s : A -> Prop) : term33 A x s.
Proof. exact (@lem7603071 A x s). Qed.
Lemma lem7603073 {A : Type'} (x : A) (s : A -> Prop) : (term33 A x s) = (term34 A x s).
Proof. exact (eq_refl (term33 A x s)). Qed.
Lemma lem7603074 {A : Type'} (x : A) (s : A -> Prop) : term34 A x s.
Proof. exact (EQ_MP (@lem7603073 A x s) (@lem7603072 A x s)). Qed.
Lemma lem7603075 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7603076 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term35 A x s.
Proof. exact (@lem7603074 A x s (@lem7603075 A s h1)). Qed.
Lemma lem7603077 {A : Type'} (x : A) (s : A -> Prop) : (term35 A x s) = ((term35 A x s) = True).
Proof. exact (@lem7 (term35 A x s)). Qed.
Lemma lem7603078 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term35 A x s) = True.
Proof. exact (EQ_MP (@lem7603077 A x s) (@lem7603076 A x s h1)). Qed.
Lemma lem7603084 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem7603085 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem7603087 {_100044 : Type'} (s : _100044 -> Prop) : term36 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem7603088 {_100044 : Type'} (s : _100044 -> Prop) : (term36 _100044 s) = (term37 _100044 s).
Proof. exact (eq_refl (term36 _100044 s)). Qed.
Lemma lem7603089 {_100044 : Type'} (s : _100044 -> Prop) : term37 _100044 s.
Proof. exact (EQ_MP (@lem7603088 _100044 s) (@lem7603087 _100044 s)). Qed.
Lemma lem7603090 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term38 _100044 s n.
Proof. exact (@lem7603089 _100044 s n). Qed.
Lemma lem7603091 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term38 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term39 _100044 s n)).
Proof. exact (eq_refl (term38 _100044 s n)). Qed.
Lemma lem7603093 {A : Type'} (x : A) : term40 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem7603094 {A : Type'} (x : A) : (term40 A x) = (term41 A x).
Proof. exact (eq_refl (term40 A x)). Qed.
Lemma lem7603095 {A : Type'} (x : A) : term41 A x.
Proof. exact (EQ_MP (@lem7603094 A x) (@lem7603093 A x)). Qed.
Lemma lem7603096 {A : Type'} (x : A) : term42 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem7603108 {A : Type'} (x : A) : term43 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem7603109 {A : Type'} (x : A) : (term43 A x) = (term44 A x).
Proof. exact (eq_refl (term43 A x)). Qed.
Lemma lem7603110 {A : Type'} (x : A) : term44 A x.
Proof. exact (EQ_MP (@lem7603109 A x) (@lem7603108 A x)). Qed.
Lemma lem7603111 {A : Type'} (x : A) (y : A) : term45 A x y.
Proof. exact (@lem7603110 A x y). Qed.
Lemma lem7603112 {A : Type'} (x : A) (y : A) : (term45 A x y) = ((term46 A x y) = (x = y)).
Proof. exact (eq_refl (term45 A x y)). Qed.
Lemma lem7603114 {A : Type'} (x : A) : term47 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem7603115 {A : Type'} (x : A) : (term47 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term47 A x)). Qed.
Lemma lem7603116 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem7603115 A x) (@lem7603114 A x)). Qed.
Lemma lem7603117 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem7603119 {A : Type'} (s : A -> Prop) : term48 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem7603120 {A : Type'} (s : A -> Prop) : (term48 A s) = (term49 A s).
Proof. exact (eq_refl (term48 A s)). Qed.
Lemma lem7603121 {A : Type'} (s : A -> Prop) : term49 A s.
Proof. exact (EQ_MP (@lem7603120 A s) (@lem7603119 A s)). Qed.
Lemma lem7603122 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term50 A s t.
Proof. exact (@lem7603121 A s t). Qed.
Lemma lem7603123 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = ((s = t) = (term51 A s t)).
Proof. exact (eq_refl (term50 A s t)). Qed.
Lemma lem7603125 (h1 : (@UNIV unit) = (@INSERT unit tt (@EMPTY unit))) : (@UNIV unit) = (@INSERT unit tt (@EMPTY unit)).
Proof. exact (h1). Qed.
Lemma lem7603126 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem7603127 (h1 : (@UNIV unit) = (@INSERT unit tt (@EMPTY unit))) : term53 = term54.
Proof. exact (MK_COMB (@lem7603126) (@lem7603125 h1)). Qed.
Lemma lem7603128 : term54 = term55.
Proof. exact (eq_refl term54). Qed.
Lemma lem7603129 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem7603130 : (term53 = term54) = (term53 = term55).
Proof. exact (MK_COMB (@lem7603129) (@lem7603128)). Qed.
Lemma lem7603131 : term53 = term57.
Proof. exact (eq_refl term53). Qed.
Lemma lem7603132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7603133 : term56 = term58.
Proof. exact (MK_COMB (@lem7603132) (@lem7603131)). Qed.
Lemma lem7603134 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem7603135 : (term53 = term55) = (term57 = term55).
Proof. exact (MK_COMB (@lem7603133) (@lem7603134)). Qed.
Lemma lem7603136 : (term53 = term54) = (term57 = term55).
Proof. exact (TRANS (@lem7603130) (@lem7603135)). Qed.
Lemma lem7603137 (h1 : (@UNIV unit) = (@INSERT unit tt (@EMPTY unit))) : term57 = term55.
Proof. exact (EQ_MP (@lem7603136) (@lem7603127 h1)). Qed.
Lemma lem7603138 (h1 : (@UNIV unit) = (@INSERT unit tt (@EMPTY unit))) : term55 = term57.
Proof. exact (SYM (@lem7603137 h1)). Qed.
Lemma lem7603142 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term51 A s t).
Proof. exact (EQ_MP (@lem7603123 A s t) (@lem7603122 A s t)). Qed.
Lemma lem7603143 (s : unit -> Prop) (t : unit -> Prop) : (s = t) = (term59 s t).
Proof. exact (@lem7603142 unit s t). Qed.
Lemma lem7603144 : ((@UNIV unit) = (@INSERT unit tt (@EMPTY unit))) = term60.
Proof. exact (@lem7603143 (@UNIV unit) (@INSERT unit tt (@EMPTY unit))). Qed.
Lemma lem7603154 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7603117 A x) (@lem7603116 A x)). Qed.
Lemma lem7603155 (x : unit) : (@IN unit x (@UNIV unit)) = True.
Proof. exact (@lem7603154 unit x). Qed.
Lemma lem7603156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7603157 (x : unit) : (term61 x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7603156) (@lem7603155 x)). Qed.
Lemma lem7603159 {A : Type'} (x : A) (y : A) : (term46 A x y) = (x = y).
Proof. exact (EQ_MP (@lem7603112 A x y) (@lem7603111 A x y)). Qed.
Lemma lem7603160 (x : unit) (y : unit) : (term62 x y) = (x = y).
Proof. exact (@lem7603159 unit x y). Qed.
Lemma lem7603161 (x : unit) : (term63 x) = (x = tt).
Proof. exact (@lem7603160 x tt). Qed.
Lemma lem7603166 (x : unit) : ((@IN unit x (@UNIV unit)) = (term63 x)) = (True = (x = tt)).
Proof. exact (MK_COMB (@lem7603157 x) (@lem7603161 x)). Qed.
Lemma lem7603168 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7603169 (x : unit) : (True = (x = tt)) = (x = tt).
Proof. exact (@lem7603168 (x = tt)). Qed.
Lemma lem7603174 (x : unit) : ((@IN unit x (@UNIV unit)) = (term63 x)) = (x = tt).
Proof. exact (TRANS (@lem7603166 x) (@lem7603169 x)). Qed.
Lemma lem7603175 : term64 = term65.
Proof. exact (fun_ext (fun x : unit => @lem7603174 x)). Qed.
Lemma lem7603176 : (@all unit) = (@all unit).
Proof. exact (eq_refl (@all unit)). Qed.
Lemma lem7603177 : term60 = term66.
Proof. exact (MK_COMB (@lem7603176) (@lem7603175)). Qed.
Lemma lem7603182 : ((@UNIV unit) = (@INSERT unit tt (@EMPTY unit))) = term66.
Proof. exact (TRANS (@lem7603144) (@lem7603177)). Qed.
Lemma lem7603183 : term66 = ((@UNIV unit) = (@INSERT unit tt (@EMPTY unit))).
Proof. exact (SYM (@lem7603182)). Qed.
Lemma lem7603185 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7603186 : term66 = term68.
Proof. exact (@lem7603185 term66). Qed.
Lemma lem7603187 : term68 = term66.
Proof. exact (SYM (@lem7603186)). Qed.
Lemma lem7603188 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem7603191 (h1 : term70) : term70.
Proof. exact (h1). Qed.
Lemma lem7603192 : term71.
Proof. exact (fun h0 : term70 => @lem7603191 h0). Qed.
Lemma lem7603193 (h1 : term71) : term71.
Proof. exact (h1). Qed.
Lemma lem7603194 (h1 : term70) : term70.
Proof. exact (h1). Qed.
Lemma lem7603195 (h1 : term70) (h2 : term71) : term70.
Proof. exact (@lem7603193 h2 (@lem7603194 h1)). Qed.
Lemma lem7603196 (h1 : term70) : term72.
Proof. exact (fun h0 : term71 => @lem7603195 h1 h0). Qed.
Lemma lem7603197 (h1 : term71) : term71.
Proof. exact (h1). Qed.
Lemma lem7603198 (h1 : term70) (h2 : term71) : term70.
Proof. exact (@lem7603196 h1 (@lem7603197 h2)). Qed.
Lemma lem7603199 (h1 : term71) : term71.
Proof. exact (fun h0 : term70 => @lem7603198 h0 h1). Qed.
Lemma lem7603200 : term73.
Proof. exact (fun h0 : term71 => @lem7603199 h0). Qed.
Lemma lem7603203 : term71.
Proof. exact (@lem7603200 (@lem7603192)). Qed.
Lemma lem7603211 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7603212 : term74 = term69.
Proof. exact (@lem7603211 term66). Qed.
Lemma lem7603217 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem7603218 : term70 = term76.
Proof. exact (MK_COMB (@lem7603217) (@lem7603212)). Qed.
Lemma lem7603220 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem16474 t)). Qed.
Lemma lem7603221 : term76 = True.
Proof. exact (@lem7603220 term69). Qed.
Lemma lem7603224 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem7603225 : term77 = (term76 = True).
Proof. exact (eq_refl term77). Qed.
Lemma lem7603226 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem7603227 : (term77 = term77) = (term77 = (term76 = True)).
Proof. exact (MK_COMB (@lem7603226) (@lem7603225)). Qed.
Lemma lem7603228 : term77 = (term76 = True).
Proof. exact (eq_refl term77). Qed.
Lemma lem7603229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7603230 : term78 = term79.
Proof. exact (MK_COMB (@lem7603229) (@lem7603228)). Qed.
Lemma lem7603231 : (term76 = True) = (term76 = True).
Proof. exact (eq_refl (term76 = True)). Qed.
Lemma lem7603232 : (term77 = (term76 = True)) = ((term76 = True) = (term76 = True)).
Proof. exact (MK_COMB (@lem7603230) (@lem7603231)). Qed.
Lemma lem7603233 : (term77 = term77) = ((term76 = True) = (term76 = True)).
Proof. exact (TRANS (@lem7603227) (@lem7603232)). Qed.
Lemma lem7603234 : (term76 = True) = (term76 = True).
Proof. exact (EQ_MP (@lem7603233) (@lem7603224)). Qed.
Lemma lem7603235 : term76 = True.
Proof. exact (EQ_MP (@lem7603234) (@lem7603221)). Qed.
Lemma lem7603244 : term70 = True.
Proof. exact (TRANS (@lem7603218) (@lem7603235)). Qed.
Lemma lem7603245 : True = term70.
Proof. exact (SYM (@lem7603244)). Qed.
Lemma lem7603246 : term70.
Proof. exact (EQ_MP (@lem7603245) (@lem0)). Qed.
Lemma lem7603248 : term70.
Proof. exact (@lem7603203 (@lem7603246)). Qed.
Lemma lem7603249 (h1 : term69) : term74.
Proof. exact (@lem7603248 (@lem7603188 h1)). Qed.
Lemma lem7603250 (h1 : term69) : False.
Proof. exact (@lem7603249 h1 (@lem15881)). Qed.
Lemma lem7603251 (h1 : term69) : term69 = False.
Proof. exact (prop_ext (fun h2 : term69 => @lem7603250 h1) (fun h2 : False => @lem7603188 h1)). Qed.
Lemma lem7603252 (h1 : term69) : False.
Proof. exact (EQ_MP (@lem7603251 h1) (@lem7603188 h1)). Qed.
Lemma lem7603253 : term68.
Proof. exact (fun h0 : term69 => @lem7603252 h0). Qed.
Lemma lem7603254 : term66.
Proof. exact (EQ_MP (@lem7603187) (@lem7603253)). Qed.
Lemma lem7603255 : (@UNIV unit) = (@INSERT unit tt (@EMPTY unit)).
Proof. exact (EQ_MP (@lem7603183) (@lem7603254)). Qed.
Lemma lem7603257 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term39 _100044 s n).
Proof. exact (EQ_MP (@lem7603091 _100044 s n) (@lem7603090 _100044 s n)). Qed.
Lemma lem7603258 (s : unit -> Prop) (n : nat) : (@HAS_SIZE unit s n) = (term80 s n).
Proof. exact (@lem7603257 unit s n). Qed.
Lemma lem7603259 : term55 = term81.
Proof. exact (@lem7603258 (@INSERT unit tt (@EMPTY unit)) term82). Qed.
Lemma lem7603263 {A : Type'} (x : A) (s : A -> Prop) : term83 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem7603078 A x s h0). Qed.
Lemma lem7603264 (x : unit) (s : unit -> Prop) : term84 x s.
Proof. exact (@lem7603263 unit x s). Qed.
Lemma lem7603265 : term85.
Proof. exact (@lem7603264 tt (@EMPTY unit)). Qed.
Lemma lem7603267 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem7603085 A) (@lem7603084 A)). Qed.
Lemma lem7603268 : (@FINITE unit (@EMPTY unit)) = True.
Proof. exact (@lem7603267 unit). Qed.
Lemma lem7603269 : True = (@FINITE unit (@EMPTY unit)).
Proof. exact (SYM (@lem7603268)). Qed.
Lemma lem7603270 : @FINITE unit (@EMPTY unit).
Proof. exact (EQ_MP (@lem7603269) (@lem0)). Qed.
Lemma lem7603271 : term86 = True.
Proof. exact (@lem7603265 (@lem7603270)). Qed.
Lemma lem7603272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7603273 : term87 = (and True).
Proof. exact (MK_COMB (@lem7603272) (@lem7603271)). Qed.
Lemma lem7603277 {A : Type'} (x : A) (s : A -> Prop) : term27 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem7603061 A x s h0). Qed.
Lemma lem7603278 (x : unit) (s : unit -> Prop) : term88 x s.
Proof. exact (@lem7603277 unit x s). Qed.
Lemma lem7603279 : term89.
Proof. exact (@lem7603278 tt (@EMPTY unit)). Qed.
Lemma lem7603281 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem7603085 A) (@lem7603084 A)). Qed.
Lemma lem7603282 : (@FINITE unit (@EMPTY unit)) = True.
Proof. exact (@lem7603281 unit). Qed.
Lemma lem7603283 : True = (@FINITE unit (@EMPTY unit)).
Proof. exact (SYM (@lem7603282)). Qed.
Lemma lem7603284 : @FINITE unit (@EMPTY unit).
Proof. exact (EQ_MP (@lem7603283) (@lem0)). Qed.
Lemma lem7603285 : term90 = term91.
Proof. exact (@lem7603279 (@lem7603284)). Qed.
Lemma lem7603287 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term92 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7603288 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term93 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7603287 _2963 g t e g' t' e'). Qed.
Lemma lem7603289 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term94 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7603288 _2963 g t e g' t'). Qed.
Lemma lem7603290 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term95 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7603289 _2963 g t e g'). Qed.
Lemma lem7603291 (g : Prop) (t : nat) (e : nat) : term96 g t e.
Proof. exact (@lem7603290 nat g t e). Qed.
Lemma lem7603292 : term97.
Proof. exact (@lem7603291 (@IN unit tt (@EMPTY unit)) (@CARD unit (@EMPTY unit)) term98). Qed.
Lemma lem7603293 (g' : Prop) : term99 g'.
Proof. exact (@lem7603292 g'). Qed.
Lemma lem7603294 (g' : Prop) : (term99 g') = (term100 g').
Proof. exact (eq_refl (term99 g')). Qed.
Lemma lem7603295 (g' : Prop) : term100 g'.
Proof. exact (EQ_MP (@lem7603294 g') (@lem7603293 g')). Qed.
Lemma lem7603296 (g' : Prop) (t' : nat) : term101 g' t'.
Proof. exact (@lem7603295 g' t'). Qed.
Lemma lem7603297 (g' : Prop) (t' : nat) : (term101 g' t') = (term102 g' t').
Proof. exact (eq_refl (term101 g' t')). Qed.
Lemma lem7603298 (g' : Prop) (t' : nat) : term102 g' t'.
Proof. exact (EQ_MP (@lem7603297 g' t') (@lem7603296 g' t')). Qed.
Lemma lem7603299 (g' : Prop) (t' : nat) (e' : nat) : term103 g' t' e'.
Proof. exact (@lem7603298 g' t' e'). Qed.
Lemma lem7603300 (g' : Prop) (t' : nat) (e' : nat) : (term103 g' t' e') = (term104 g' t' e').
Proof. exact (eq_refl (term103 g' t' e')). Qed.
Lemma lem7603301 (g' : Prop) (t' : nat) (e' : nat) : term104 g' t' e'.
Proof. exact (EQ_MP (@lem7603300 g' t' e') (@lem7603299 g' t' e')). Qed.
Lemma lem7603303 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7603096 A x (@lem7603095 A x)). Qed.
Lemma lem7603304 (x : unit) : (@IN unit x (@EMPTY unit)) = False.
Proof. exact (@lem7603303 unit x). Qed.
Lemma lem7603305 : (@IN unit tt (@EMPTY unit)) = False.
Proof. exact (@lem7603304 tt). Qed.
Lemma lem7603306 (t' : nat) (e' : nat) : term105 t' e'.
Proof. exact (@lem7603301 False t' e'). Qed.
Lemma lem7603307 (t' : nat) (e' : nat) : term106 t' e'.
Proof. exact (@lem7603306 t' e' (@lem7603305)). Qed.
Lemma lem7603312 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem7603313 : (@CARD unit (@EMPTY unit)) = (NUMERAL 0).
Proof. exact (@lem7603312 unit). Qed.
Lemma lem7603314 : term107.
Proof. exact (fun h0 : False => @lem7603313). Qed.
Lemma lem7603315 (e' : nat) : term108 e'.
Proof. exact (@lem7603307 (NUMERAL 0) e'). Qed.
Lemma lem7603316 (e' : nat) : term109 e'.
Proof. exact (@lem7603315 e' (@lem7603314)). Qed.
Lemma lem7603323 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem7603324 : (@CARD unit (@EMPTY unit)) = (NUMERAL 0).
Proof. exact (@lem7603323 unit). Qed.
Lemma lem7603325 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem7603326 : term98 = term110.
Proof. exact (MK_COMB (@lem7603325) (@lem7603324)). Qed.
Lemma lem7603328 (n : nat) : (term21 n) = (term22 n).
Proof. exact (EQ_MP (@lem7603048 n) (@lem7603047 n)). Qed.
Lemma lem7603329 : term110 = term111.
Proof. exact (@lem7603328 0). Qed.
Lemma lem7603331 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem7603035)). Qed.
Lemma lem7603332 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem7603333 : term111 = term82.
Proof. exact (MK_COMB (@lem7603332) (@lem7603331)). Qed.
Lemma lem7603334 : term110 = term82.
Proof. exact (TRANS (@lem7603329) (@lem7603333)). Qed.
Lemma lem7603335 : term98 = term82.
Proof. exact (TRANS (@lem7603326) (@lem7603334)). Qed.
Lemma lem7603336 : term112.
Proof. exact (fun h0 : ~ False => @lem7603335). Qed.
Lemma lem7603337 : term113.
Proof. exact (@lem7603316 term82). Qed.
Lemma lem7603338 : term91 = term114.
Proof. exact (@lem7603337 (@lem7603336)). Qed.
Lemma lem7603340 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7603341 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7603340 nat t1 t2). Qed.
Lemma lem7603342 : term114 = term82.
Proof. exact (@lem7603341 (NUMERAL 0) term82). Qed.
Lemma lem7603343 : term91 = term82.
Proof. exact (TRANS (@lem7603338) (@lem7603342)). Qed.
Lemma lem7603344 : term90 = term82.
Proof. exact (TRANS (@lem7603285) (@lem7603343)). Qed.
Lemma lem7603345 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7603346 : term115 = term116.
Proof. exact (MK_COMB (@lem7603345) (@lem7603344)). Qed.
Lemma lem7603347 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem7603348 : (term90 = term82) = (term82 = term82).
Proof. exact (MK_COMB (@lem7603346) (@lem7603347)). Qed.
Lemma lem7603350 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem7602801 m n) (@lem7602800 m n)). Qed.
Lemma lem7603351 : (term82 = term82) = ((BIT1 0) = (BIT1 0)).
Proof. exact (@lem7603350 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7603353 (m : nat) (n : nat) : ((BIT1 m) = (BIT1 n)) = (m = n).
Proof. exact (EQ_MP (@lem7602756 m n) (@lem7602755 m n)). Qed.
Lemma lem7603354 : ((BIT1 0) = (BIT1 0)) = (0 = 0).
Proof. exact (@lem7603353 0 0). Qed.
Lemma lem7603356 : (0 = 0) = True.
Proof. exact (proj1 (@lem7602743)). Qed.
Lemma lem7603357 : ((BIT1 0) = (BIT1 0)) = True.
Proof. exact (TRANS (@lem7603354) (@lem7603356)). Qed.
Lemma lem7603358 : (term82 = term82) = True.
Proof. exact (TRANS (@lem7603351) (@lem7603357)). Qed.
Lemma lem7603359 : (term90 = term82) = True.
Proof. exact (TRANS (@lem7603348) (@lem7603358)). Qed.
Lemma lem7603360 : term81 = (True /\ True).
Proof. exact (MK_COMB (@lem7603273) (@lem7603359)). Qed.
Lemma lem7603362 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7603363 : (True /\ True) = True.
Proof. exact (@lem7603362 True). Qed.
Lemma lem7603364 : term81 = True.
Proof. exact (TRANS (@lem7603360) (@lem7603363)). Qed.
Lemma lem7603365 : term55 = True.
Proof. exact (TRANS (@lem7603259) (@lem7603364)). Qed.
Lemma lem7603366 : True = term55.
Proof. exact (SYM (@lem7603365)). Qed.
Lemma lem7603367 : term55.
Proof. exact (EQ_MP (@lem7603366) (@lem0)). Qed.
Lemma lem7603368 (h1 : (@UNIV unit) = (@INSERT unit tt (@EMPTY unit))) : term57.
Proof. exact (EQ_MP (@lem7603138 h1) (@lem7603367)). Qed.
Lemma lem7603369 : ((@UNIV unit) = (@INSERT unit tt (@EMPTY unit))) = term57.
Proof. exact (prop_ext (fun h1 : (@UNIV unit) = (@INSERT unit tt (@EMPTY unit)) => @lem7603368 h1) (fun h1 : term57 => @lem7603255)). Qed.
Lemma lem7603370 : term57.
Proof. exact (EQ_MP (@lem7603369) (@lem7603255)). Qed.
