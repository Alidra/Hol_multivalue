Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_LT_term_abbrevs.
Require Import LE_0_spec.
Require Import LE_SUC_spec.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Require Import thm89994_spec.
Lemma lem97962 (n : nat) : term0 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem97963 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem97964 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem97963 n) (@lem97962 n)). Qed.
Lemma lem97965 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem97969 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem97970 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem97969 n h1)). Qed.
Lemma lem97971 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem97972 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem97971 n h1)). Qed.
Lemma lem97973 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem97970 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem97972 n h1)). Qed.
Lemma lem97974 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem97975 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem97974) (@lem97973 n)). Qed.
Lemma lem97976 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem97975 n)). Qed.
Lemma lem97977 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97978 : term6 = term7.
Proof. exact (MK_COMB (@lem97977) (@lem97976)). Qed.
Lemma lem97979 : term7.
Proof. exact (EQ_MP (@lem97978) (@lem75570)). Qed.
Lemma lem97980 (n : nat) : term8 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem97981 (n : nat) : (term8 n) = (term9 n).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem97982 (n : nat) : term9 n.
Proof. exact (EQ_MP (@lem97981 n) (@lem97980 n)). Qed.
Lemma lem97983 (n : nat) : (term9 n) = ((term9 n) = True).
Proof. exact (@lem7 (term9 n)). Qed.
Lemma lem97985 (n : nat) : term10 n.
Proof. exact (@lem97979 n). Qed.
Lemma lem97986 (n : nat) : (term10 n) = (term3 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem97987 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem97986 n) (@lem97985 n)). Qed.
Lemma lem97991 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem97992 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem97991 n h1)). Qed.
Lemma lem97993 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem97994 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem97993 n h1)). Qed.
Lemma lem97995 (n : nat) : ((NUMERAL 0) = (S n)) = ((S n) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h1 : (NUMERAL 0) = (S n) => @lem97992 n h1) (fun h1 : (S n) = (NUMERAL 0) => @lem97994 n h1)). Qed.
Lemma lem97996 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem97997 (n : nat) : (term3 n) = (term2 n).
Proof. exact (MK_COMB (@lem97996) (@lem97995 n)). Qed.
Lemma lem97998 (n : nat) : term2 n.
Proof. exact (EQ_MP (@lem97997 n) (@lem97987 n)). Qed.
Lemma lem97999 (n : nat) : term11 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem98017 : term12.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem98018 (m : nat) : term13 m.
Proof. exact (@lem98017 m). Qed.
Lemma lem98019 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem98020 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem98019 m) (@lem98018 m)). Qed.
Lemma lem98021 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem98020 m n). Qed.
Lemma lem98022 (m : nat) (n : nat) : (term15 m n) = ((term16 m n) = (term17 m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem98024 : term18.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem98025 (m : nat) : term19 m.
Proof. exact (@lem98024 m). Qed.
Lemma lem98026 (m : nat) : (term19 m) = ((term20 m) = False).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem98035 : term21.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem98036 (m : nat) : term22 m.
Proof. exact (@lem98035 m). Qed.
Lemma lem98037 (m : nat) : (term22 m) = ((term23 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem98040 (P : nat -> Prop) : term24 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem98041 : term25.
Proof. exact (@lem98040 term26). Qed.
Lemma lem98042 : term27 = term28.
Proof. exact (eq_refl term27). Qed.
Lemma lem98043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem98044 : term29 = term30.
Proof. exact (MK_COMB (@lem98043) (@lem98042)). Qed.
Lemma lem98045 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem98046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98047 (m : nat) : (term33 m) = (term34 m).
Proof. exact (MK_COMB (@lem98046) (@lem98045 m)). Qed.
Lemma lem98048 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem98049 (m : nat) : (term37 m) = (term38 m).
Proof. exact (MK_COMB (@lem98047 m) (@lem98048 m)). Qed.
Lemma lem98050 : term39 = term40.
Proof. exact (fun_ext (fun m : nat => @lem98049 m)). Qed.
Lemma lem98051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98052 : term41 = term42.
Proof. exact (MK_COMB (@lem98051) (@lem98050)). Qed.
Lemma lem98053 : term43 = term44.
Proof. exact (MK_COMB (@lem98044) (@lem98052)). Qed.
Lemma lem98054 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98055 : term45 = term46.
Proof. exact (MK_COMB (@lem98054) (@lem98053)). Qed.
Lemma lem98056 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem98057 : term47 = term26.
Proof. exact (fun_ext (fun m : nat => @lem98056 m)). Qed.
Lemma lem98058 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98059 : term48 = term49.
Proof. exact (MK_COMB (@lem98058) (@lem98057)). Qed.
Lemma lem98060 : term25 = term50.
Proof. exact (MK_COMB (@lem98055) (@lem98059)). Qed.
Lemma lem98061 : term50.
Proof. exact (EQ_MP (@lem98060) (@lem98041)). Qed.
Lemma lem98062 (m : nat) (h1 : term32 m) : term32 m.
Proof. exact (h1). Qed.
Lemma lem98064 (P : nat -> Prop) : term24 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem98065 : term51.
Proof. exact (@lem98064 term52). Qed.
Lemma lem98066 : term53 = (term54 = term55).
Proof. exact (eq_refl term53). Qed.
Lemma lem98067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem98068 : term56 = term57.
Proof. exact (MK_COMB (@lem98067) (@lem98066)). Qed.
Lemma lem98069 (n : nat) : (term58 n) = ((term59 n) = (term23 n)).
Proof. exact (eq_refl (term58 n)). Qed.
Lemma lem98070 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98071 (n : nat) : (term60 n) = (term61 n).
Proof. exact (MK_COMB (@lem98070) (@lem98069 n)). Qed.
Lemma lem98072 (n : nat) : (term62 n) = ((term63 n) = (term64 n)).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem98073 (n : nat) : (term65 n) = (term66 n).
Proof. exact (MK_COMB (@lem98071 n) (@lem98072 n)). Qed.
Lemma lem98074 : term67 = term68.
Proof. exact (fun_ext (fun n : nat => @lem98073 n)). Qed.
Lemma lem98075 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98076 : term69 = term70.
Proof. exact (MK_COMB (@lem98075) (@lem98074)). Qed.
Lemma lem98077 : term71 = term72.
Proof. exact (MK_COMB (@lem98068) (@lem98076)). Qed.
Lemma lem98078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98079 : term73 = term74.
Proof. exact (MK_COMB (@lem98078) (@lem98077)). Qed.
Lemma lem98080 (n : nat) : (term58 n) = ((term59 n) = (term23 n)).
Proof. exact (eq_refl (term58 n)). Qed.
Lemma lem98081 : term75 = term52.
Proof. exact (fun_ext (fun n : nat => @lem98080 n)). Qed.
Lemma lem98082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98083 : term76 = term28.
Proof. exact (MK_COMB (@lem98082) (@lem98081)). Qed.
Lemma lem98084 : term51 = term77.
Proof. exact (MK_COMB (@lem98079) (@lem98083)). Qed.
Lemma lem98085 : term77.
Proof. exact (EQ_MP (@lem98084) (@lem98065)). Qed.
Lemma lem98092 (P : nat -> Prop) : term24 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem98093 (m : nat) : term78 m.
Proof. exact (@lem98092 (term79 m)). Qed.
Lemma lem98094 (m : nat) : (term80 m) = ((term81 m) = (term82 m)).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem98095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem98096 (m : nat) : (term83 m) = (term84 m).
Proof. exact (MK_COMB (@lem98095) (@lem98094 m)). Qed.
Lemma lem98097 (n : nat) (m : nat) : (term85 m n) = ((term86 m n) = (term87 n m)).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem98098 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98099 (n : nat) (m : nat) : (term88 m n) = (term89 n m).
Proof. exact (MK_COMB (@lem98098) (@lem98097 n m)). Qed.
Lemma lem98100 (n : nat) (m : nat) : (term90 m n) = ((term91 m n) = (term92 n m)).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem98101 (n : nat) (m : nat) : (term93 m n) = (term94 n m).
Proof. exact (MK_COMB (@lem98099 n m) (@lem98100 n m)). Qed.
Lemma lem98102 (m : nat) : (term95 m) = (term96 m).
Proof. exact (fun_ext (fun n : nat => @lem98101 n m)). Qed.
Lemma lem98103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98104 (m : nat) : (term97 m) = (term98 m).
Proof. exact (MK_COMB (@lem98103) (@lem98102 m)). Qed.
Lemma lem98105 (m : nat) : (term99 m) = (term100 m).
Proof. exact (MK_COMB (@lem98096 m) (@lem98104 m)). Qed.
Lemma lem98106 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98107 (m : nat) : (term101 m) = (term102 m).
Proof. exact (MK_COMB (@lem98106) (@lem98105 m)). Qed.
Lemma lem98108 (n : nat) (m : nat) : (term85 m n) = ((term86 m n) = (term87 n m)).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem98109 (m : nat) : (term103 m) = (term79 m).
Proof. exact (fun_ext (fun n : nat => @lem98108 n m)). Qed.
Lemma lem98110 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98111 (m : nat) : (term104 m) = (term36 m).
Proof. exact (MK_COMB (@lem98110) (@lem98109 m)). Qed.
Lemma lem98112 (m : nat) : (term78 m) = (term105 m).
Proof. exact (MK_COMB (@lem98107 m) (@lem98111 m)). Qed.
Lemma lem98113 (m : nat) : term105 m.
Proof. exact (EQ_MP (@lem98112 m) (@lem98093 m)). Qed.
Lemma lem98170 (m : nat) : term106 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem98171 (m : nat) : (term106 m) = (term107 m).
Proof. exact (eq_refl (term106 m)). Qed.
Lemma lem98172 (m : nat) : term107 m.
Proof. exact (EQ_MP (@lem98171 m) (@lem98170 m)). Qed.
Lemma lem98173 (m : nat) (n : nat) : term108 m n.
Proof. exact (@lem98172 m n). Qed.
Lemma lem98174 (m : nat) (n : nat) : (term108 m n) = ((term109 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term108 m n)). Qed.
Lemma lem98176 (m : nat) : term110 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem98177 (m : nat) : (term110 m) = (term111 m).
Proof. exact (eq_refl (term110 m)). Qed.
Lemma lem98178 (m : nat) : term111 m.
Proof. exact (EQ_MP (@lem98177 m) (@lem98176 m)). Qed.
Lemma lem98179 (m : nat) (n : nat) : term112 m n.
Proof. exact (@lem98178 m n). Qed.
Lemma lem98180 (m : nat) (n : nat) : (term112 m n) = ((term92 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term112 m n)). Qed.
Lemma lem98182 (n : nat) (m : nat) (h1 : term32 m) : term113 m n.
Proof. exact (@lem98062 m h1 n). Qed.
Lemma lem98183 (n : nat) (m : nat) : (term113 m n) = ((term114 m n) = (Peano.le n m)).
Proof. exact (eq_refl (term113 m n)). Qed.
Lemma lem98188 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem98174 m n) (@lem98173 m n)). Qed.
Lemma lem98189 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem98190 (m : nat) (n : nat) : (term91 m n) = (term114 m n).
Proof. exact (MK_COMB (@lem98189) (@lem98188 m n)). Qed.
Lemma lem98192 (n : nat) (m : nat) (h1 : term32 m) : (term114 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem98183 n m) (@lem98182 n m h1)). Qed.
Lemma lem98193 (n : nat) (m : nat) (h1 : term32 m) : (term91 m n) = (Peano.le n m).
Proof. exact (TRANS (@lem98190 m n) (@lem98192 n m h1)). Qed.
Lemma lem98194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem98195 (n : nat) (m : nat) (h1 : term32 m) : (term115 m n) = (term116 n m).
Proof. exact (MK_COMB (@lem98194) (@lem98193 n m h1)). Qed.
Lemma lem98197 (m : nat) (n : nat) : (term92 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem98180 m n) (@lem98179 m n)). Qed.
Lemma lem98198 (n : nat) (m : nat) : (term92 n m) = (Peano.le n m).
Proof. exact (@lem98197 n m). Qed.
Lemma lem98199 (n : nat) (m : nat) (h1 : term32 m) : ((term91 m n) = (term92 n m)) = ((Peano.le n m) = (Peano.le n m)).
Proof. exact (MK_COMB (@lem98195 n m h1) (@lem98198 n m)). Qed.
Lemma lem98201 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem98202 (x : Prop) : (x = x) = True.
Proof. exact (@lem98201 Prop x). Qed.
Lemma lem98203 (n : nat) (m : nat) : ((Peano.le n m) = (Peano.le n m)) = True.
Proof. exact (@lem98202 (Peano.le n m)). Qed.
Lemma lem98204 (n : nat) (m : nat) (h1 : term32 m) : ((term91 m n) = (term92 n m)) = True.
Proof. exact (TRANS (@lem98199 n m h1) (@lem98203 n m)). Qed.
Lemma lem98205 (n : nat) (m : nat) (h1 : term32 m) : True = ((term91 m n) = (term92 n m)).
Proof. exact (SYM (@lem98204 n m h1)). Qed.
Lemma lem98206 (n : nat) (m : nat) (h1 : term32 m) : (term91 m n) = (term92 n m).
Proof. exact (EQ_MP (@lem98205 n m h1) (@lem0)). Qed.
Lemma lem98210 (m : nat) : (term20 m) = False.
Proof. exact (EQ_MP (@lem98026 m) (@lem98025 m)). Qed.
Lemma lem98211 : term117 = False.
Proof. exact (@lem98210 (NUMERAL 0)). Qed.
Lemma lem98212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem98213 : term54 = (~ False).
Proof. exact (MK_COMB (@lem98212) (@lem98211)). Qed.
Lemma lem98215 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem98216 : term54 = True.
Proof. exact (TRANS (@lem98213) (@lem98215)). Qed.
Lemma lem98217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem98218 : term118 = (@eq Prop True).
Proof. exact (MK_COMB (@lem98217) (@lem98216)). Qed.
Lemma lem98220 (n : nat) : (term9 n) = True.
Proof. exact (EQ_MP (@lem97983 n) (@lem97982 n)). Qed.
Lemma lem98221 : term55 = True.
Proof. exact (@lem98220 (NUMERAL 0)). Qed.
Lemma lem98222 : (term54 = term55) = (True = True).
Proof. exact (MK_COMB (@lem98218) (@lem98221)). Qed.
Lemma lem98224 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem98225 : (True = True) = True.
Proof. exact (@lem98224 True). Qed.
Lemma lem98226 : (term54 = term55) = True.
Proof. exact (TRANS (@lem98222) (@lem98225)). Qed.
Lemma lem98227 : True = (term54 = term55).
Proof. exact (SYM (@lem98226)). Qed.
Lemma lem98232 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem98022 m n) (@lem98021 m n)). Qed.
Lemma lem98233 (n : nat) : (term1 n) = (term119 n).
Proof. exact (@lem98232 (NUMERAL 0) n). Qed.
Lemma lem98238 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem98239 (n : nat) : (term63 n) = (term120 n).
Proof. exact (MK_COMB (@lem98238) (@lem98233 n)). Qed.
Lemma lem98240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem98241 (n : nat) : (term121 n) = (term122 n).
Proof. exact (MK_COMB (@lem98240) (@lem98239 n)). Qed.
Lemma lem98243 (m : nat) : (term23 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem98037 m) (@lem98036 m)). Qed.
Lemma lem98244 (n : nat) : (term64 n) = ((S n) = (NUMERAL 0)).
Proof. exact (@lem98243 (S n)). Qed.
Lemma lem98246 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem97999 n (@lem97998 n)). Qed.
Lemma lem98247 (n : nat) : (term64 n) = False.
Proof. exact (TRANS (@lem98244 n) (@lem98246 n)). Qed.
Lemma lem98248 (n : nat) : ((term63 n) = (term64 n)) = ((term120 n) = False).
Proof. exact (MK_COMB (@lem98241 n) (@lem98247 n)). Qed.
Lemma lem98250 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem98251 (n : nat) : ((term120 n) = False) = (term123 n).
Proof. exact (@lem98250 (term120 n)). Qed.
Lemma lem98253 (t : Prop) : (term124 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem98254 (n : nat) : (term123 n) = (term119 n).
Proof. exact (@lem98253 (term119 n)). Qed.
Lemma lem98259 (n : nat) : ((term120 n) = False) = (term119 n).
Proof. exact (TRANS (@lem98251 n) (@lem98254 n)). Qed.
Lemma lem98260 (n : nat) : ((term63 n) = (term64 n)) = (term119 n).
Proof. exact (TRANS (@lem98248 n) (@lem98259 n)). Qed.
Lemma lem98261 (n : nat) : (term119 n) = ((term63 n) = (term64 n)).
Proof. exact (SYM (@lem98260 n)). Qed.
Lemma lem98265 (m : nat) : (term20 m) = False.
Proof. exact (EQ_MP (@lem98026 m) (@lem98025 m)). Qed.
Lemma lem98266 (m : nat) : (term125 m) = False.
Proof. exact (@lem98265 (S m)). Qed.
Lemma lem98267 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem98268 (m : nat) : (term81 m) = (~ False).
Proof. exact (MK_COMB (@lem98267) (@lem98266 m)). Qed.
Lemma lem98270 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem98271 (m : nat) : (term81 m) = True.
Proof. exact (TRANS (@lem98268 m) (@lem98270)). Qed.
Lemma lem98272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem98273 (m : nat) : (term126 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem98272) (@lem98271 m)). Qed.
Lemma lem98275 (n : nat) : (term9 n) = True.
Proof. exact (EQ_MP (@lem97983 n) (@lem97982 n)). Qed.
Lemma lem98276 (m : nat) : (term82 m) = True.
Proof. exact (@lem98275 (S m)). Qed.
Lemma lem98277 (m : nat) : ((term81 m) = (term82 m)) = (True = True).
Proof. exact (MK_COMB (@lem98273 m) (@lem98276 m)). Qed.
Lemma lem98279 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem98280 : (True = True) = True.
Proof. exact (@lem98279 True). Qed.
Lemma lem98281 (m : nat) : ((term81 m) = (term82 m)) = True.
Proof. exact (TRANS (@lem98277 m) (@lem98280)). Qed.
Lemma lem98282 (m : nat) : True = ((term81 m) = (term82 m)).
Proof. exact (SYM (@lem98281 m)). Qed.
Lemma lem98285 (P : nat -> Prop) : term24 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem98286 : term127.
Proof. exact (@lem98285 term128). Qed.
Lemma lem98287 : term129 = term130.
Proof. exact (eq_refl term129). Qed.
Lemma lem98288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem98289 : term131 = term132.
Proof. exact (MK_COMB (@lem98288) (@lem98287)). Qed.
Lemma lem98290 (n : nat) : (term133 n) = (term119 n).
Proof. exact (eq_refl (term133 n)). Qed.
Lemma lem98291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98292 (n : nat) : (term134 n) = (term135 n).
Proof. exact (MK_COMB (@lem98291) (@lem98290 n)). Qed.
Lemma lem98293 (n : nat) : (term136 n) = (term137 n).
Proof. exact (eq_refl (term136 n)). Qed.
Lemma lem98294 (n : nat) : (term138 n) = (term139 n).
Proof. exact (MK_COMB (@lem98292 n) (@lem98293 n)). Qed.
Lemma lem98295 : term140 = term141.
Proof. exact (fun_ext (fun n : nat => @lem98294 n)). Qed.
Lemma lem98296 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98297 : term142 = term143.
Proof. exact (MK_COMB (@lem98296) (@lem98295)). Qed.
Lemma lem98298 : term144 = term145.
Proof. exact (MK_COMB (@lem98289) (@lem98297)). Qed.
Lemma lem98299 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98300 : term146 = term147.
Proof. exact (MK_COMB (@lem98299) (@lem98298)). Qed.
Lemma lem98301 (n : nat) : (term133 n) = (term119 n).
Proof. exact (eq_refl (term133 n)). Qed.
Lemma lem98302 : term148 = term128.
Proof. exact (fun_ext (fun n : nat => @lem98301 n)). Qed.
Lemma lem98303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98304 : term149 = term150.
Proof. exact (MK_COMB (@lem98303) (@lem98302)). Qed.
Lemma lem98305 : term127 = term151.
Proof. exact (MK_COMB (@lem98300) (@lem98304)). Qed.
Lemma lem98306 : term151.
Proof. exact (EQ_MP (@lem98305) (@lem98286)). Qed.
Lemma lem98311 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem98312 (x : nat) : (x = x) = True.
Proof. exact (@lem98311 nat x). Qed.
Lemma lem98313 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem98312 (NUMERAL 0)). Qed.
Lemma lem98314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem98315 : term152 = (or True).
Proof. exact (MK_COMB (@lem98314) (@lem98313)). Qed.
Lemma lem98316 : term117 = term117.
Proof. exact (eq_refl term117). Qed.
Lemma lem98317 : term130 = term153.
Proof. exact (MK_COMB (@lem98315) (@lem98316)). Qed.
Lemma lem98319 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem98320 : term153 = True.
Proof. exact (@lem98319 term117). Qed.
Lemma lem98321 : term130 = True.
Proof. exact (TRANS (@lem98317) (@lem98320)). Qed.
Lemma lem98322 : True = term130.
Proof. exact (SYM (@lem98321)). Qed.
Lemma lem98323 : term130.
Proof. exact (EQ_MP (@lem98322) (@lem0)). Qed.
Lemma lem98329 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem97965 n) (@lem97964 n)). Qed.
Lemma lem98330 (n' : nat) : (term1 n') = True.
Proof. exact (@lem98329 n'). Qed.
Lemma lem98331 (n' : nat) : (term154 n') = (term154 n').
Proof. exact (eq_refl (term154 n')). Qed.
Lemma lem98332 (n' : nat) : (term137 n') = (term155 n').
Proof. exact (MK_COMB (@lem98331 n') (@lem98330 n')). Qed.
Lemma lem98334 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem98335 (n' : nat) : (term155 n') = True.
Proof. exact (@lem98334 ((NUMERAL 0) = (S n'))). Qed.
Lemma lem98336 (n' : nat) : (term137 n') = True.
Proof. exact (TRANS (@lem98332 n') (@lem98335 n')). Qed.
Lemma lem98337 (n' : nat) : True = (term137 n').
Proof. exact (SYM (@lem98336 n')). Qed.
Lemma lem98338 (n' : nat) : term137 n'.
Proof. exact (EQ_MP (@lem98337 n') (@lem0)). Qed.
Lemma lem98339 (n' : nat) : term139 n'.
Proof. exact (fun h0 : term119 n' => @lem98338 n'). Qed.
Lemma lem98344 : term143.
Proof. exact (fun n' : nat => @lem98339 n'). Qed.
Lemma lem98345 : term145.
Proof. exact (conj (@lem98323) (@lem98344)). Qed.
Lemma lem98346 : term150.
Proof. exact (@lem98306 (@lem98345)). Qed.
Lemma lem98347 (n : nat) : term133 n.
Proof. exact (@lem98346 n). Qed.
Lemma lem98348 (n : nat) : (term133 n) = (term119 n).
Proof. exact (eq_refl (term133 n)). Qed.
Lemma lem98349 (n : nat) : term119 n.
Proof. exact (EQ_MP (@lem98348 n) (@lem98347 n)). Qed.
Lemma lem98351 (m : nat) : (term81 m) = (term82 m).
Proof. exact (EQ_MP (@lem98282 m) (@lem0)). Qed.
Lemma lem98352 (n : nat) : (term63 n) = (term64 n).
Proof. exact (EQ_MP (@lem98261 n) (@lem98349 n)). Qed.
Lemma lem98353 : term54 = term55.
Proof. exact (EQ_MP (@lem98227) (@lem0)). Qed.
Lemma lem98354 (n : nat) (m : nat) (h1 : term32 m) : term94 n m.
Proof. exact (fun h0 : (term86 m n) = (term87 n m) => @lem98206 n m h1). Qed.
Lemma lem98359 (m : nat) (h1 : term32 m) : term98 m.
Proof. exact (fun n : nat => @lem98354 n m h1). Qed.
Lemma lem98360 (m : nat) (h1 : term32 m) : term100 m.
Proof. exact (conj (@lem98351 m) (@lem98359 m h1)). Qed.
Lemma lem98361 (m : nat) (h1 : term32 m) : term36 m.
Proof. exact (@lem98113 m (@lem98360 m h1)). Qed.
Lemma lem98362 (n : nat) : term66 n.
Proof. exact (fun h0 : (term59 n) = (term23 n) => @lem98352 n). Qed.
Lemma lem98367 : term70.
Proof. exact (fun n : nat => @lem98362 n). Qed.
Lemma lem98368 : term72.
Proof. exact (conj (@lem98353) (@lem98367)). Qed.
Lemma lem98369 : term28.
Proof. exact (@lem98085 (@lem98368)). Qed.
Lemma lem98370 (m : nat) : term38 m.
Proof. exact (fun h0 : term32 m => @lem98361 m h0). Qed.
Lemma lem98375 : term42.
Proof. exact (fun m : nat => @lem98370 m). Qed.
Lemma lem98376 : term44.
Proof. exact (conj (@lem98369) (@lem98375)). Qed.
Lemma lem98377 : term49.
Proof. exact (@lem98061 (@lem98376)). Qed.
