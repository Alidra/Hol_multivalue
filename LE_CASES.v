Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_CASES_term_abbrevs.
Require Import LE_0_spec.
Require Import LE_SUC_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem95943 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem95944 : term1.
Proof. exact (@lem95943 term2). Qed.
Lemma lem95945 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem95946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95947 : term5 = term6.
Proof. exact (MK_COMB (@lem95946) (@lem95945)). Qed.
Lemma lem95948 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem95949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95950 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem95949) (@lem95948 m)). Qed.
Lemma lem95951 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem95952 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem95950 m) (@lem95951 m)). Qed.
Lemma lem95953 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem95952 m)). Qed.
Lemma lem95954 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95955 : term17 = term18.
Proof. exact (MK_COMB (@lem95954) (@lem95953)). Qed.
Lemma lem95956 : term19 = term20.
Proof. exact (MK_COMB (@lem95947) (@lem95955)). Qed.
Lemma lem95957 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95958 : term21 = term22.
Proof. exact (MK_COMB (@lem95957) (@lem95956)). Qed.
Lemma lem95959 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem95960 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem95959 m)). Qed.
Lemma lem95961 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95962 : term24 = term25.
Proof. exact (MK_COMB (@lem95961) (@lem95960)). Qed.
Lemma lem95963 : term1 = term26.
Proof. exact (MK_COMB (@lem95958) (@lem95962)). Qed.
Lemma lem95964 : term26.
Proof. exact (EQ_MP (@lem95963) (@lem95944)). Qed.
Lemma lem95965 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem95967 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem95968 : term27.
Proof. exact (@lem95967 term28). Qed.
Lemma lem95969 : term29 = term30.
Proof. exact (eq_refl term29). Qed.
Lemma lem95970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95971 : term31 = term32.
Proof. exact (MK_COMB (@lem95970) (@lem95969)). Qed.
Lemma lem95972 (n : nat) : (term33 n) = (term34 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem95973 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95974 (n : nat) : (term35 n) = (term36 n).
Proof. exact (MK_COMB (@lem95973) (@lem95972 n)). Qed.
Lemma lem95975 (n : nat) : (term37 n) = (term38 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem95976 (n : nat) : (term39 n) = (term40 n).
Proof. exact (MK_COMB (@lem95974 n) (@lem95975 n)). Qed.
Lemma lem95977 : term41 = term42.
Proof. exact (fun_ext (fun n : nat => @lem95976 n)). Qed.
Lemma lem95978 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95979 : term43 = term44.
Proof. exact (MK_COMB (@lem95978) (@lem95977)). Qed.
Lemma lem95980 : term45 = term46.
Proof. exact (MK_COMB (@lem95971) (@lem95979)). Qed.
Lemma lem95981 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem95982 : term47 = term48.
Proof. exact (MK_COMB (@lem95981) (@lem95980)). Qed.
Lemma lem95983 (n : nat) : (term33 n) = (term34 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem95984 : term49 = term28.
Proof. exact (fun_ext (fun n : nat => @lem95983 n)). Qed.
Lemma lem95985 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem95986 : term50 = term4.
Proof. exact (MK_COMB (@lem95985) (@lem95984)). Qed.
Lemma lem95987 : term27 = term51.
Proof. exact (MK_COMB (@lem95982) (@lem95986)). Qed.
Lemma lem95988 : term51.
Proof. exact (EQ_MP (@lem95987) (@lem95968)). Qed.
Lemma lem95995 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem95996 (m : nat) : term52 m.
Proof. exact (@lem95995 (term53 m)). Qed.
Lemma lem95997 (m : nat) : (term54 m) = (term55 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem95998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem95999 (m : nat) : (term56 m) = (term57 m).
Proof. exact (MK_COMB (@lem95998) (@lem95997 m)). Qed.
Lemma lem96000 (n : nat) (m : nat) : (term58 m n) = (term59 n m).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem96001 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96002 (n : nat) (m : nat) : (term60 m n) = (term61 n m).
Proof. exact (MK_COMB (@lem96001) (@lem96000 n m)). Qed.
Lemma lem96003 (n : nat) (m : nat) : (term62 m n) = (term63 n m).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem96004 (n : nat) (m : nat) : (term64 m n) = (term65 n m).
Proof. exact (MK_COMB (@lem96002 n m) (@lem96003 n m)). Qed.
Lemma lem96005 (m : nat) : (term66 m) = (term67 m).
Proof. exact (fun_ext (fun n : nat => @lem96004 n m)). Qed.
Lemma lem96006 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96007 (m : nat) : (term68 m) = (term69 m).
Proof. exact (MK_COMB (@lem96006) (@lem96005 m)). Qed.
Lemma lem96008 (m : nat) : (term70 m) = (term71 m).
Proof. exact (MK_COMB (@lem95999 m) (@lem96007 m)). Qed.
Lemma lem96009 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96010 (m : nat) : (term72 m) = (term73 m).
Proof. exact (MK_COMB (@lem96009) (@lem96008 m)). Qed.
Lemma lem96011 (n : nat) (m : nat) : (term58 m n) = (term59 n m).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem96012 (m : nat) : (term74 m) = (term53 m).
Proof. exact (fun_ext (fun n : nat => @lem96011 n m)). Qed.
Lemma lem96013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96014 (m : nat) : (term75 m) = (term12 m).
Proof. exact (MK_COMB (@lem96013) (@lem96012 m)). Qed.
Lemma lem96015 (m : nat) : (term52 m) = (term76 m).
Proof. exact (MK_COMB (@lem96010 m) (@lem96014 m)). Qed.
Lemma lem96016 (m : nat) : term76 m.
Proof. exact (EQ_MP (@lem96015 m) (@lem95996 m)). Qed.
Lemma lem96028 (n : nat) : term77 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem96029 (n : nat) : (term77 n) = (term78 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem96030 (n : nat) : term78 n.
Proof. exact (EQ_MP (@lem96029 n) (@lem96028 n)). Qed.
Lemma lem96031 (n : nat) : (term78 n) = ((term78 n) = True).
Proof. exact (@lem7 (term78 n)). Qed.
Lemma lem96034 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem96035 : term30 = term79.
Proof. exact (@lem96034 term79). Qed.
Lemma lem96037 (n : nat) : (term78 n) = True.
Proof. exact (EQ_MP (@lem96031 n) (@lem96030 n)). Qed.
Lemma lem96038 : term79 = True.
Proof. exact (@lem96037 (NUMERAL 0)). Qed.
Lemma lem96039 : term30 = True.
Proof. exact (TRANS (@lem96035) (@lem96038)). Qed.
Lemma lem96040 : True = term30.
Proof. exact (SYM (@lem96039)). Qed.
Lemma lem96041 : term30.
Proof. exact (EQ_MP (@lem96040) (@lem0)). Qed.
Lemma lem96048 (n : nat) : term77 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem96049 (n : nat) : (term77 n) = (term78 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem96050 (n : nat) : term78 n.
Proof. exact (EQ_MP (@lem96049 n) (@lem96048 n)). Qed.
Lemma lem96051 (n : nat) : (term78 n) = ((term78 n) = True).
Proof. exact (@lem7 (term78 n)). Qed.
Lemma lem96058 (n : nat) : (term78 n) = True.
Proof. exact (EQ_MP (@lem96051 n) (@lem96050 n)). Qed.
Lemma lem96059 (n : nat) : (term80 n) = True.
Proof. exact (@lem96058 (S n)). Qed.
Lemma lem96060 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96061 (n : nat) : (term81 n) = (or True).
Proof. exact (MK_COMB (@lem96060) (@lem96059 n)). Qed.
Lemma lem96062 (n : nat) : (term82 n) = (term82 n).
Proof. exact (eq_refl (term82 n)). Qed.
Lemma lem96063 (n : nat) : (term38 n) = (term83 n).
Proof. exact (MK_COMB (@lem96061 n) (@lem96062 n)). Qed.
Lemma lem96065 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem96066 (n : nat) : (term83 n) = True.
Proof. exact (@lem96065 (term82 n)). Qed.
Lemma lem96067 (n : nat) : (term38 n) = True.
Proof. exact (TRANS (@lem96063 n) (@lem96066 n)). Qed.
Lemma lem96068 (n : nat) : True = (term38 n).
Proof. exact (SYM (@lem96067 n)). Qed.
Lemma lem96069 (n : nat) : term38 n.
Proof. exact (EQ_MP (@lem96068 n) (@lem0)). Qed.
Lemma lem96076 (n : nat) : term77 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem96077 (n : nat) : (term77 n) = (term78 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem96078 (n : nat) : term78 n.
Proof. exact (EQ_MP (@lem96077 n) (@lem96076 n)). Qed.
Lemma lem96079 (n : nat) : (term78 n) = ((term78 n) = True).
Proof. exact (@lem7 (term78 n)). Qed.
Lemma lem96089 (n : nat) : (term78 n) = True.
Proof. exact (EQ_MP (@lem96079 n) (@lem96078 n)). Qed.
Lemma lem96090 (m : nat) : (term80 m) = True.
Proof. exact (@lem96089 (S m)). Qed.
Lemma lem96091 (m : nat) : (term84 m) = (term84 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem96092 (m : nat) : (term55 m) = (term85 m).
Proof. exact (MK_COMB (@lem96091 m) (@lem96090 m)). Qed.
Lemma lem96094 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem96095 (m : nat) : (term85 m) = True.
Proof. exact (@lem96094 (term82 m)). Qed.
Lemma lem96096 (m : nat) : (term55 m) = True.
Proof. exact (TRANS (@lem96092 m) (@lem96095 m)). Qed.
Lemma lem96097 (m : nat) : True = (term55 m).
Proof. exact (SYM (@lem96096 m)). Qed.
Lemma lem96098 (m : nat) : term55 m.
Proof. exact (EQ_MP (@lem96097 m) (@lem0)). Qed.
Lemma lem96099 (m : nat) : term86 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem96100 (m : nat) : (term86 m) = (term87 m).
Proof. exact (eq_refl (term86 m)). Qed.
Lemma lem96101 (m : nat) : term87 m.
Proof. exact (EQ_MP (@lem96100 m) (@lem96099 m)). Qed.
Lemma lem96102 (m : nat) (n : nat) : term88 m n.
Proof. exact (@lem96101 m n). Qed.
Lemma lem96103 (m : nat) (n : nat) : (term88 m n) = ((term89 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term88 m n)). Qed.
Lemma lem96110 (n : nat) (m : nat) (h1 : term8 m) : term90 m n.
Proof. exact (@lem95965 m h1 n). Qed.
Lemma lem96111 (n : nat) (m : nat) : (term90 m n) = (term91 n m).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem96112 (n : nat) (m : nat) (h1 : term8 m) : term91 n m.
Proof. exact (EQ_MP (@lem96111 n m) (@lem96110 n m h1)). Qed.
Lemma lem96113 (n : nat) (m : nat) : (term91 n m) = ((term91 n m) = True).
Proof. exact (@lem7 (term91 n m)). Qed.
Lemma lem96120 (m : nat) (n : nat) : (term89 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem96103 m n) (@lem96102 m n)). Qed.
Lemma lem96121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96122 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (MK_COMB (@lem96121) (@lem96120 m n)). Qed.
Lemma lem96124 (m : nat) (n : nat) : (term89 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem96103 m n) (@lem96102 m n)). Qed.
Lemma lem96125 (n : nat) (m : nat) : (term89 n m) = (Peano.le n m).
Proof. exact (@lem96124 n m). Qed.
Lemma lem96126 (n : nat) (m : nat) : (term63 n m) = (term91 n m).
Proof. exact (MK_COMB (@lem96122 m n) (@lem96125 n m)). Qed.
Lemma lem96128 (n : nat) (m : nat) (h1 : term8 m) : (term91 n m) = True.
Proof. exact (EQ_MP (@lem96113 n m) (@lem96112 n m h1)). Qed.
Lemma lem96129 (n : nat) (m : nat) (h1 : term8 m) : (term63 n m) = True.
Proof. exact (TRANS (@lem96126 n m) (@lem96128 n m h1)). Qed.
Lemma lem96130 (n : nat) (m : nat) (h1 : term8 m) : True = (term63 n m).
Proof. exact (SYM (@lem96129 n m h1)). Qed.
Lemma lem96131 (n : nat) (m : nat) (h1 : term8 m) : term63 n m.
Proof. exact (EQ_MP (@lem96130 n m h1) (@lem0)). Qed.
Lemma lem96132 (n : nat) (m : nat) (h1 : term8 m) : term65 n m.
Proof. exact (fun h0 : term59 n m => @lem96131 n m h1). Qed.
Lemma lem96137 (m : nat) (h1 : term8 m) : term69 m.
Proof. exact (fun n : nat => @lem96132 n m h1). Qed.
Lemma lem96138 (m : nat) (h1 : term8 m) : term71 m.
Proof. exact (conj (@lem96098 m) (@lem96137 m h1)). Qed.
Lemma lem96139 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (@lem96016 m (@lem96138 m h1)). Qed.
Lemma lem96140 (n : nat) : term40 n.
Proof. exact (fun h0 : term34 n => @lem96069 n). Qed.
Lemma lem96145 : term44.
Proof. exact (fun n : nat => @lem96140 n). Qed.
Lemma lem96146 : term46.
Proof. exact (conj (@lem96041) (@lem96145)). Qed.
Lemma lem96147 : term4.
Proof. exact (@lem95988 (@lem96146)). Qed.
Lemma lem96148 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem96139 m h0). Qed.
Lemma lem96153 : term18.
Proof. exact (fun m : nat => @lem96148 m). Qed.
Lemma lem96154 : term20.
Proof. exact (conj (@lem96147) (@lem96153)). Qed.
Lemma lem96155 : term25.
Proof. exact (@lem95964 (@lem96154)). Qed.
