Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_LE_ANTISYM_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1319377_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_eq_spec.
Require Import treal_le_spec.
Lemma lem1329972 (x : hreal) : term0 x.
Proof. exact (@lem1319377 x). Qed.
Lemma lem1329973 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1329974 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1329973 x) (@lem1329972 x)). Qed.
Lemma lem1329975 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1329974 x y). Qed.
Lemma lem1329976 (x : hreal) (y : hreal) : (term2 x y) = ((term3 y x) = (x = y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1329978 (x1 : hreal) : term4 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1329979 (x1 : hreal) : (term4 x1) = (term5 x1).
Proof. exact (eq_refl (term4 x1)). Qed.
Lemma lem1329980 (x1 : hreal) : term5 x1.
Proof. exact (EQ_MP (@lem1329979 x1) (@lem1329978 x1)). Qed.
Lemma lem1329981 (x1 : hreal) (y2 : hreal) : term6 x1 y2.
Proof. exact (@lem1329980 x1 y2). Qed.
Lemma lem1329982 (x1 : hreal) (y2 : hreal) : (term6 x1 y2) = (term7 x1 y2).
Proof. exact (eq_refl (term6 x1 y2)). Qed.
Lemma lem1329983 (x1 : hreal) (y2 : hreal) : term7 x1 y2.
Proof. exact (EQ_MP (@lem1329982 x1 y2) (@lem1329981 x1 y2)). Qed.
Lemma lem1329984 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term8 x1 y2 x2.
Proof. exact (@lem1329983 x1 y2 x2). Qed.
Lemma lem1329985 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term8 x1 y2 x2) = (term9 x1 y2 x2).
Proof. exact (eq_refl (term8 x1 y2 x2)). Qed.
Lemma lem1329986 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term9 x1 y2 x2.
Proof. exact (EQ_MP (@lem1329985 x1 y2 x2) (@lem1329984 x1 y2 x2)). Qed.
Lemma lem1329987 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term10 x1 y2 x2 y1.
Proof. exact (@lem1329986 x1 y2 x2 y1). Qed.
Lemma lem1329988 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term10 x1 y2 x2 y1) = ((term11 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term10 x1 y2 x2 y1)). Qed.
Lemma lem1329990 (x1 : hreal) : term12 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1329991 (x1 : hreal) : (term12 x1) = (term13 x1).
Proof. exact (eq_refl (term12 x1)). Qed.
Lemma lem1329992 (x1 : hreal) : term13 x1.
Proof. exact (EQ_MP (@lem1329991 x1) (@lem1329990 x1)). Qed.
Lemma lem1329993 (x1 : hreal) (y2 : hreal) : term14 x1 y2.
Proof. exact (@lem1329992 x1 y2). Qed.
Lemma lem1329994 (x1 : hreal) (y2 : hreal) : (term14 x1 y2) = (term15 x1 y2).
Proof. exact (eq_refl (term14 x1 y2)). Qed.
Lemma lem1329995 (x1 : hreal) (y2 : hreal) : term15 x1 y2.
Proof. exact (EQ_MP (@lem1329994 x1 y2) (@lem1329993 x1 y2)). Qed.
Lemma lem1329996 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term16 x1 y2 x2.
Proof. exact (@lem1329995 x1 y2 x2). Qed.
Lemma lem1329997 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term16 x1 y2 x2) = (term17 x1 y2 x2).
Proof. exact (eq_refl (term16 x1 y2 x2)). Qed.
Lemma lem1329998 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term17 x1 y2 x2.
Proof. exact (EQ_MP (@lem1329997 x1 y2 x2) (@lem1329996 x1 y2 x2)). Qed.
Lemma lem1329999 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term18 x1 y2 x2 y1.
Proof. exact (@lem1329998 x1 y2 x2 y1). Qed.
Lemma lem1330000 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term18 x1 y2 x2 y1) = ((term19 x1 y1 x2 y2) = (term20 x1 y2 x2 y1)).
Proof. exact (eq_refl (term18 x1 y2 x2 y1)). Qed.
Lemma lem1330002 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term21 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1330003 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = ((term22 _5106 _5107 P) = (term23 _5106 _5107 P)).
Proof. exact (eq_refl (term21 _5106 _5107 P)). Qed.
Lemma lem1330010 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term22 _5106 _5107 P) = (term23 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1330003 _5106 _5107 P) (@lem1330002 _5106 _5107 P)). Qed.
Lemma lem1330011 (P : type1233) : (term24 P) = (term25 P).
Proof. exact (@lem1330010 hreal hreal P). Qed.
Lemma lem1330012 : term26 = term27.
Proof. exact (@lem1330011 term28). Qed.
Lemma lem1330013 (x : prod hreal hreal) : (term29 x) = (term30 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1330014 : term31 = term28.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1330013 x)). Qed.
Lemma lem1330015 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1330016 : term26 = term32.
Proof. exact (MK_COMB (@lem1330015) (@lem1330014)). Qed.
Lemma lem1330017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330018 : term33 = term34.
Proof. exact (MK_COMB (@lem1330017) (@lem1330016)). Qed.
Lemma lem1330019 (p1 : hreal) (p2 : hreal) : (term35 p1 p2) = (term36 p1 p2).
Proof. exact (eq_refl (term35 p1 p2)). Qed.
Lemma lem1330020 (p1 : hreal) : (term37 p1) = (term38 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1330019 p1 p2)). Qed.
Lemma lem1330021 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330022 (p1 : hreal) : (term39 p1) = (term40 p1).
Proof. exact (MK_COMB (@lem1330021) (@lem1330020 p1)). Qed.
Lemma lem1330023 : term41 = term42.
Proof. exact (fun_ext (fun p1 : hreal => @lem1330022 p1)). Qed.
Lemma lem1330024 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330025 : term27 = term43.
Proof. exact (MK_COMB (@lem1330024) (@lem1330023)). Qed.
Lemma lem1330026 : (term26 = term27) = (term32 = term43).
Proof. exact (MK_COMB (@lem1330018) (@lem1330025)). Qed.
Lemma lem1330027 : term32 = term43.
Proof. exact (EQ_MP (@lem1330026) (@lem1330012)). Qed.
Lemma lem1330045 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term22 _5106 _5107 P) = (term23 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1330003 _5106 _5107 P) (@lem1330002 _5106 _5107 P)). Qed.
Lemma lem1330046 (P : type1233) : (term24 P) = (term25 P).
Proof. exact (@lem1330045 hreal hreal P). Qed.
Lemma lem1330047 (p1 : hreal) (p2 : hreal) : (term44 p1 p2) = (term45 p1 p2).
Proof. exact (@lem1330046 (term46 p1 p2)). Qed.
Lemma lem1330048 (p1 : hreal) (p2 : hreal) (y : prod hreal hreal) : (term47 p1 p2 y) = ((term48 y p1 p2) = (term49 p1 p2 y)).
Proof. exact (eq_refl (term47 p1 p2 y)). Qed.
Lemma lem1330049 (p1 : hreal) (p2 : hreal) : (term50 p1 p2) = (term46 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1330048 p1 p2 y)). Qed.
Lemma lem1330050 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1330051 (p1 : hreal) (p2 : hreal) : (term44 p1 p2) = (term36 p1 p2).
Proof. exact (MK_COMB (@lem1330050) (@lem1330049 p1 p2)). Qed.
Lemma lem1330052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330053 (p1 : hreal) (p2 : hreal) : (term51 p1 p2) = (term52 p1 p2).
Proof. exact (MK_COMB (@lem1330052) (@lem1330051 p1 p2)). Qed.
Lemma lem1330054 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term53 p1 p2 p1' p2') = ((term54 p1' p2' p1 p2) = (term11 p1 p2 p1' p2')).
Proof. exact (eq_refl (term53 p1 p2 p1' p2')). Qed.
Lemma lem1330055 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term55 p1 p2 p1') = (term56 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : hreal => @lem1330054 p1 p2 p1' p2')). Qed.
Lemma lem1330056 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330057 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term57 p1 p2 p1') = (term58 p1 p2 p1').
Proof. exact (MK_COMB (@lem1330056) (@lem1330055 p1 p2 p1')). Qed.
Lemma lem1330058 (p1 : hreal) (p2 : hreal) : (term59 p1 p2) = (term60 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1330057 p1 p2 p1')). Qed.
Lemma lem1330059 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330060 (p1 : hreal) (p2 : hreal) : (term45 p1 p2) = (term61 p1 p2).
Proof. exact (MK_COMB (@lem1330059) (@lem1330058 p1 p2)). Qed.
Lemma lem1330061 (p1 : hreal) (p2 : hreal) : ((term44 p1 p2) = (term45 p1 p2)) = ((term36 p1 p2) = (term61 p1 p2)).
Proof. exact (MK_COMB (@lem1330053 p1 p2) (@lem1330060 p1 p2)). Qed.
Lemma lem1330062 (p1 : hreal) (p2 : hreal) : (term36 p1 p2) = (term61 p1 p2).
Proof. exact (EQ_MP (@lem1330061 p1 p2) (@lem1330047 p1 p2)). Qed.
Lemma lem1330080 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term19 x1 y1 x2 y2) = (term20 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1330000 x1 y2 x2 y1) (@lem1329999 x1 y2 x2 y1)). Qed.
Lemma lem1330081 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term19 p1 p2 p1' p2') = (term20 p1 p2' p1' p2).
Proof. exact (@lem1330080 p1 p2' p1' p2). Qed.
Lemma lem1330082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1330083 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term62 p1 p2 p1' p2') = (term63 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1330082) (@lem1330081 p1 p2' p1' p2)). Qed.
Lemma lem1330085 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term19 x1 y1 x2 y2) = (term20 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1330000 x1 y2 x2 y1) (@lem1329999 x1 y2 x2 y1)). Qed.
Lemma lem1330086 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) : (term19 p1' p2' p1 p2) = (term20 p1' p2 p1 p2').
Proof. exact (@lem1330085 p1' p2 p1 p2'). Qed.
Lemma lem1330087 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) : (term54 p1' p2' p1 p2) = (term64 p1' p2 p1 p2').
Proof. exact (MK_COMB (@lem1330083 p1 p2' p1' p2) (@lem1330086 p1' p2 p1 p2')). Qed.
Lemma lem1330089 (x : hreal) (y : hreal) : (term3 y x) = (x = y).
Proof. exact (EQ_MP (@lem1329976 x y) (@lem1329975 x y)). Qed.
Lemma lem1330090 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term64 p1' p2 p1 p2') = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (@lem1330089 (hreal_add p1 p2') (hreal_add p1' p2)). Qed.
Lemma lem1330093 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term54 p1' p2' p1 p2) = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (TRANS (@lem1330087 p1' p2 p1 p2') (@lem1330090 p1 p2' p1' p2)). Qed.
Lemma lem1330094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330095 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term65 p1' p2' p1 p2) = (term66 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1330094) (@lem1330093 p1 p2' p1' p2)). Qed.
Lemma lem1330097 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term11 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1329988 x1 y2 x2 y1) (@lem1329987 x1 y2 x2 y1)). Qed.
Lemma lem1330098 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term11 p1 p2 p1' p2') = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (@lem1330097 p1 p2' p1' p2). Qed.
Lemma lem1330101 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : ((term54 p1' p2' p1 p2) = (term11 p1 p2 p1' p2')) = (((hreal_add p1 p2') = (hreal_add p1' p2)) = ((hreal_add p1 p2') = (hreal_add p1' p2))).
Proof. exact (MK_COMB (@lem1330095 p1 p2' p1' p2) (@lem1330098 p1 p2' p1' p2)). Qed.
Lemma lem1330103 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1330104 (x : Prop) : (x = x) = True.
Proof. exact (@lem1330103 Prop x). Qed.
Lemma lem1330105 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (((hreal_add p1 p2') = (hreal_add p1' p2)) = ((hreal_add p1 p2') = (hreal_add p1' p2))) = True.
Proof. exact (@lem1330104 ((hreal_add p1 p2') = (hreal_add p1' p2))). Qed.
Lemma lem1330106 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : ((term54 p1' p2' p1 p2) = (term11 p1 p2 p1' p2')) = True.
Proof. exact (TRANS (@lem1330101 p1 p2' p1' p2) (@lem1330105 p1 p2' p1' p2)). Qed.
Lemma lem1330107 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term56 p1 p2 p1') = term67.
Proof. exact (fun_ext (fun p2' : hreal => @lem1330106 p1 p2 p1' p2')). Qed.
Lemma lem1330108 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330109 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term58 p1 p2 p1') = term68.
Proof. exact (MK_COMB (@lem1330108) (@lem1330107 p1 p2 p1')). Qed.
Lemma lem1330111 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1330112 (t : Prop) : (term70 t) = t.
Proof. exact (@lem1330111 hreal t). Qed.
Lemma lem1330113 : term68 = True.
Proof. exact (@lem1330112 True). Qed.
Lemma lem1330114 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term58 p1 p2 p1') = True.
Proof. exact (TRANS (@lem1330109 p1 p2 p1') (@lem1330113)). Qed.
Lemma lem1330115 (p1 : hreal) (p2 : hreal) : (term60 p1 p2) = term67.
Proof. exact (fun_ext (fun p1' : hreal => @lem1330114 p1 p2 p1')). Qed.
Lemma lem1330116 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330117 (p1 : hreal) (p2 : hreal) : (term61 p1 p2) = term68.
Proof. exact (MK_COMB (@lem1330116) (@lem1330115 p1 p2)). Qed.
Lemma lem1330119 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1330120 (t : Prop) : (term70 t) = t.
Proof. exact (@lem1330119 hreal t). Qed.
Lemma lem1330121 : term68 = True.
Proof. exact (@lem1330120 True). Qed.
Lemma lem1330122 (p1 : hreal) (p2 : hreal) : (term61 p1 p2) = True.
Proof. exact (TRANS (@lem1330117 p1 p2) (@lem1330121)). Qed.
Lemma lem1330123 (p1 : hreal) (p2 : hreal) : (term36 p1 p2) = True.
Proof. exact (TRANS (@lem1330062 p1 p2) (@lem1330122 p1 p2)). Qed.
Lemma lem1330124 (p1 : hreal) : (term38 p1) = term67.
Proof. exact (fun_ext (fun p2 : hreal => @lem1330123 p1 p2)). Qed.
Lemma lem1330125 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330126 (p1 : hreal) : (term40 p1) = term68.
Proof. exact (MK_COMB (@lem1330125) (@lem1330124 p1)). Qed.
Lemma lem1330128 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1330129 (t : Prop) : (term70 t) = t.
Proof. exact (@lem1330128 hreal t). Qed.
Lemma lem1330130 : term68 = True.
Proof. exact (@lem1330129 True). Qed.
Lemma lem1330131 (p1 : hreal) : (term40 p1) = True.
Proof. exact (TRANS (@lem1330126 p1) (@lem1330130)). Qed.
Lemma lem1330132 : term42 = term67.
Proof. exact (fun_ext (fun p1 : hreal => @lem1330131 p1)). Qed.
Lemma lem1330133 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330134 : term43 = term68.
Proof. exact (MK_COMB (@lem1330133) (@lem1330132)). Qed.
Lemma lem1330136 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1330137 (t : Prop) : (term70 t) = t.
Proof. exact (@lem1330136 hreal t). Qed.
Lemma lem1330138 : term68 = True.
Proof. exact (@lem1330137 True). Qed.
Lemma lem1330139 : term43 = True.
Proof. exact (TRANS (@lem1330134) (@lem1330138)). Qed.
Lemma lem1330140 : term32 = True.
Proof. exact (TRANS (@lem1330027) (@lem1330139)). Qed.
Lemma lem1330141 : True = term32.
Proof. exact (SYM (@lem1330140)). Qed.
Lemma lem1330142 : term32.
Proof. exact (EQ_MP (@lem1330141) (@lem0)). Qed.
