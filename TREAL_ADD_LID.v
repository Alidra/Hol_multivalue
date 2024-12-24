Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_ADD_LID_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1320277_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_add_spec.
Require Import treal_eq_spec.
Require Import treal_of_num_spec.
Lemma lem1328040 (x : hreal) : term0 x.
Proof. exact (@lem1320277 x). Qed.
Lemma lem1328041 (x : hreal) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1328043 (x1 : hreal) : term2 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1328044 (x1 : hreal) : (term2 x1) = (term3 x1).
Proof. exact (eq_refl (term2 x1)). Qed.
Lemma lem1328045 (x1 : hreal) : term3 x1.
Proof. exact (EQ_MP (@lem1328044 x1) (@lem1328043 x1)). Qed.
Lemma lem1328046 (x1 : hreal) (y2 : hreal) : term4 x1 y2.
Proof. exact (@lem1328045 x1 y2). Qed.
Lemma lem1328047 (x1 : hreal) (y2 : hreal) : (term4 x1 y2) = (term5 x1 y2).
Proof. exact (eq_refl (term4 x1 y2)). Qed.
Lemma lem1328048 (x1 : hreal) (y2 : hreal) : term5 x1 y2.
Proof. exact (EQ_MP (@lem1328047 x1 y2) (@lem1328046 x1 y2)). Qed.
Lemma lem1328049 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term6 x1 y2 x2.
Proof. exact (@lem1328048 x1 y2 x2). Qed.
Lemma lem1328050 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term6 x1 y2 x2) = (term7 x1 y2 x2).
Proof. exact (eq_refl (term6 x1 y2 x2)). Qed.
Lemma lem1328051 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term7 x1 y2 x2.
Proof. exact (EQ_MP (@lem1328050 x1 y2 x2) (@lem1328049 x1 y2 x2)). Qed.
Lemma lem1328052 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term8 x1 y2 x2 y1.
Proof. exact (@lem1328051 x1 y2 x2 y1). Qed.
Lemma lem1328053 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term8 x1 y2 x2 y1) = ((term9 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term8 x1 y2 x2 y1)). Qed.
Lemma lem1328055 (x1 : hreal) : term10 x1.
Proof. exact (@lem1323802 x1). Qed.
Lemma lem1328056 (x1 : hreal) : (term10 x1) = (term11 x1).
Proof. exact (eq_refl (term10 x1)). Qed.
Lemma lem1328057 (x1 : hreal) : term11 x1.
Proof. exact (EQ_MP (@lem1328056 x1) (@lem1328055 x1)). Qed.
Lemma lem1328058 (x1 : hreal) (x2 : hreal) : term12 x1 x2.
Proof. exact (@lem1328057 x1 x2). Qed.
Lemma lem1328059 (x1 : hreal) (x2 : hreal) : (term12 x1 x2) = (term13 x1 x2).
Proof. exact (eq_refl (term12 x1 x2)). Qed.
Lemma lem1328060 (x1 : hreal) (x2 : hreal) : term13 x1 x2.
Proof. exact (EQ_MP (@lem1328059 x1 x2) (@lem1328058 x1 x2)). Qed.
Lemma lem1328061 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term14 x1 x2 y1.
Proof. exact (@lem1328060 x1 x2 y1). Qed.
Lemma lem1328062 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term14 x1 x2 y1) = (term15 x1 x2 y1).
Proof. exact (eq_refl (term14 x1 x2 y1)). Qed.
Lemma lem1328063 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term15 x1 x2 y1.
Proof. exact (EQ_MP (@lem1328062 x1 x2 y1) (@lem1328061 x1 x2 y1)). Qed.
Lemma lem1328064 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : term16 x1 x2 y1 y2.
Proof. exact (@lem1328063 x1 x2 y1 y2). Qed.
Lemma lem1328065 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term16 x1 x2 y1 y2) = ((term17 x1 y1 x2 y2) = (term18 x1 x2 y1 y2)).
Proof. exact (eq_refl (term16 x1 x2 y1 y2)). Qed.
Lemma lem1328067 (n : nat) : term19 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1328068 (n : nat) : (term19 n) = ((treal_of_num n) = (term20 n)).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem1328070 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term21 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1328071 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = ((term22 _5106 _5107 P) = (term23 _5106 _5107 P)).
Proof. exact (eq_refl (term21 _5106 _5107 P)). Qed.
Lemma lem1328078 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term22 _5106 _5107 P) = (term23 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1328071 _5106 _5107 P) (@lem1328070 _5106 _5107 P)). Qed.
Lemma lem1328079 (P : type1233) : (term24 P) = (term25 P).
Proof. exact (@lem1328078 hreal hreal P). Qed.
Lemma lem1328080 : term26 = term27.
Proof. exact (@lem1328079 term28). Qed.
Lemma lem1328081 (x : prod hreal hreal) : (term29 x) = (term30 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1328082 : term31 = term28.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1328081 x)). Qed.
Lemma lem1328083 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1328084 : term26 = term32.
Proof. exact (MK_COMB (@lem1328083) (@lem1328082)). Qed.
Lemma lem1328085 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1328086 : term33 = term34.
Proof. exact (MK_COMB (@lem1328085) (@lem1328084)). Qed.
Lemma lem1328087 (p1 : hreal) (p2 : hreal) : (term35 p1 p2) = (term36 p1 p2).
Proof. exact (eq_refl (term35 p1 p2)). Qed.
Lemma lem1328088 (p1 : hreal) : (term37 p1) = (term38 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1328087 p1 p2)). Qed.
Lemma lem1328089 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328090 (p1 : hreal) : (term39 p1) = (term40 p1).
Proof. exact (MK_COMB (@lem1328089) (@lem1328088 p1)). Qed.
Lemma lem1328091 : term41 = term42.
Proof. exact (fun_ext (fun p1 : hreal => @lem1328090 p1)). Qed.
Lemma lem1328092 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328093 : term27 = term43.
Proof. exact (MK_COMB (@lem1328092) (@lem1328091)). Qed.
Lemma lem1328094 : (term26 = term27) = (term32 = term43).
Proof. exact (MK_COMB (@lem1328086) (@lem1328093)). Qed.
Lemma lem1328095 : term32 = term43.
Proof. exact (EQ_MP (@lem1328094) (@lem1328080)). Qed.
Lemma lem1328109 (n : nat) : (treal_of_num n) = (term20 n).
Proof. exact (EQ_MP (@lem1328068 n) (@lem1328067 n)). Qed.
Lemma lem1328110 : term44 = term45.
Proof. exact (@lem1328109 (NUMERAL 0)). Qed.
Lemma lem1328111 : treal_add = treal_add.
Proof. exact (eq_refl treal_add). Qed.
Lemma lem1328112 : term46 = term47.
Proof. exact (MK_COMB (@lem1328111) (@lem1328110)). Qed.
Lemma lem1328113 (p1 : hreal) (p2 : hreal) : (@pair hreal hreal p1 p2) = (@pair hreal hreal p1 p2).
Proof. exact (eq_refl (@pair hreal hreal p1 p2)). Qed.
Lemma lem1328114 (p1 : hreal) (p2 : hreal) : (term48 p1 p2) = (term49 p1 p2).
Proof. exact (MK_COMB (@lem1328112) (@lem1328113 p1 p2)). Qed.
Lemma lem1328116 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term17 x1 y1 x2 y2) = (term18 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1328065 x1 x2 y1 y2) (@lem1328064 x1 x2 y1 y2)). Qed.
Lemma lem1328117 (p1 : hreal) (p2 : hreal) : (term49 p1 p2) = (term50 p1 p2).
Proof. exact (@lem1328116 term51 p1 term51 p2). Qed.
Lemma lem1328119 (x : hreal) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1328041 x) (@lem1328040 x)). Qed.
Lemma lem1328120 (p1 : hreal) : (term1 p1) = p1.
Proof. exact (@lem1328119 p1). Qed.
Lemma lem1328121 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1328122 (p1 : hreal) : (term52 p1) = (@pair hreal hreal p1).
Proof. exact (MK_COMB (@lem1328121) (@lem1328120 p1)). Qed.
Lemma lem1328124 (x : hreal) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1328041 x) (@lem1328040 x)). Qed.
Lemma lem1328125 (p2 : hreal) : (term1 p2) = p2.
Proof. exact (@lem1328124 p2). Qed.
Lemma lem1328126 (p1 : hreal) (p2 : hreal) : (term50 p1 p2) = (@pair hreal hreal p1 p2).
Proof. exact (MK_COMB (@lem1328122 p1) (@lem1328125 p2)). Qed.
Lemma lem1328127 (p1 : hreal) (p2 : hreal) : (term49 p1 p2) = (@pair hreal hreal p1 p2).
Proof. exact (TRANS (@lem1328117 p1 p2) (@lem1328126 p1 p2)). Qed.
Lemma lem1328128 (p1 : hreal) (p2 : hreal) : (term48 p1 p2) = (@pair hreal hreal p1 p2).
Proof. exact (TRANS (@lem1328114 p1 p2) (@lem1328127 p1 p2)). Qed.
Lemma lem1328129 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1328130 (p1 : hreal) (p2 : hreal) : (term53 p1 p2) = (term54 p1 p2).
Proof. exact (MK_COMB (@lem1328129) (@lem1328128 p1 p2)). Qed.
Lemma lem1328131 (p1 : hreal) (p2 : hreal) : (@pair hreal hreal p1 p2) = (@pair hreal hreal p1 p2).
Proof. exact (eq_refl (@pair hreal hreal p1 p2)). Qed.
Lemma lem1328132 (p1 : hreal) (p2 : hreal) : (term36 p1 p2) = (term55 p1 p2).
Proof. exact (MK_COMB (@lem1328130 p1 p2) (@lem1328131 p1 p2)). Qed.
Lemma lem1328134 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term9 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1328053 x1 y2 x2 y1) (@lem1328052 x1 y2 x2 y1)). Qed.
Lemma lem1328135 (p1 : hreal) (p2 : hreal) : (term55 p1 p2) = ((hreal_add p1 p2) = (hreal_add p1 p2)).
Proof. exact (@lem1328134 p1 p2 p1 p2). Qed.
Lemma lem1328137 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1328138 (x : hreal) : (x = x) = True.
Proof. exact (@lem1328137 hreal x). Qed.
Lemma lem1328139 (p1 : hreal) (p2 : hreal) : ((hreal_add p1 p2) = (hreal_add p1 p2)) = True.
Proof. exact (@lem1328138 (hreal_add p1 p2)). Qed.
Lemma lem1328140 (p1 : hreal) (p2 : hreal) : (term55 p1 p2) = True.
Proof. exact (TRANS (@lem1328135 p1 p2) (@lem1328139 p1 p2)). Qed.
Lemma lem1328141 (p1 : hreal) (p2 : hreal) : (term36 p1 p2) = True.
Proof. exact (TRANS (@lem1328132 p1 p2) (@lem1328140 p1 p2)). Qed.
Lemma lem1328142 (p1 : hreal) : (term38 p1) = term56.
Proof. exact (fun_ext (fun p2 : hreal => @lem1328141 p1 p2)). Qed.
Lemma lem1328143 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328144 (p1 : hreal) : (term40 p1) = term57.
Proof. exact (MK_COMB (@lem1328143) (@lem1328142 p1)). Qed.
Lemma lem1328146 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328147 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1328146 hreal t). Qed.
Lemma lem1328148 : term57 = True.
Proof. exact (@lem1328147 True). Qed.
Lemma lem1328149 (p1 : hreal) : (term40 p1) = True.
Proof. exact (TRANS (@lem1328144 p1) (@lem1328148)). Qed.
Lemma lem1328150 : term42 = term56.
Proof. exact (fun_ext (fun p1 : hreal => @lem1328149 p1)). Qed.
Lemma lem1328151 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328152 : term43 = term57.
Proof. exact (MK_COMB (@lem1328151) (@lem1328150)). Qed.
Lemma lem1328154 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328155 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1328154 hreal t). Qed.
Lemma lem1328156 : term57 = True.
Proof. exact (@lem1328155 True). Qed.
Lemma lem1328157 : term43 = True.
Proof. exact (TRANS (@lem1328152) (@lem1328156)). Qed.
Lemma lem1328158 : term32 = True.
Proof. exact (TRANS (@lem1328095) (@lem1328157)). Qed.
Lemma lem1328159 : True = term32.
Proof. exact (SYM (@lem1328158)). Qed.
Lemma lem1328160 : term32.
Proof. exact (EQ_MP (@lem1328159) (@lem0)). Qed.
