Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_INV_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import MULT_CLAUSES_spec.
Require Import NADD_MUL_LINV_LEMMA8_spec.
Require Import NADD_OF_NUM_spec.
Require Import is_nadd_spec.
Require Import nadd_inv_spec.
Require Import thm0_spec.
Require Import thm1262760_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1308009 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1308010 (x : nadd) (h1 : term0) : term1 x.
Proof. exact (@lem1308009 h1 x). Qed.
Lemma lem1308011 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1308012 (x : nadd) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1308011 x) (@lem1308010 x h1)). Qed.
Lemma lem1308013 (x : nadd) (h1 : term3 x) : term3 x.
Proof. exact (h1). Qed.
Lemma lem1308014 (x : nadd) (h1 : term0) (h2 : term3 x) : term4 x.
Proof. exact (@lem1308012 x h1 (@lem1308013 x h2)). Qed.
Lemma lem1308015 (x : nadd) (h1 : term3 x) : term5 x.
Proof. exact (fun h0 : term0 => @lem1308014 x h0 h1). Qed.
Lemma lem1308016 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1308017 (x : nadd) (h1 : term0) (h2 : term3 x) : term4 x.
Proof. exact (@lem1308015 x h2 (@lem1308016 h1)). Qed.
Lemma lem1308018 (x : nadd) (h1 : term0) : term2 x.
Proof. exact (fun h0 : term3 x => @lem1308017 x h1 h0). Qed.
Lemma lem1308019 (h1 : term0) : term0.
Proof. exact (fun x : nadd => @lem1308018 x h1). Qed.
Lemma lem1308020 : term6.
Proof. exact (fun h0 : term0 => @lem1308019 h0). Qed.
Lemma lem1308021 : term0.
Proof. exact (@lem1308020 (@lem1307531)). Qed.
Lemma lem1308022 (x : nadd) : term1 x.
Proof. exact (@lem1308021 x). Qed.
Lemma lem1308023 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1308025 (r : nat -> nat) (h1 : (is_nadd r) = ((term7 r) = r)) : (is_nadd r) = ((term7 r) = r).
Proof. exact (h1). Qed.
Lemma lem1308026 (r : nat -> nat) (h1 : (is_nadd r) = ((term7 r) = r)) : ((term7 r) = r) = (is_nadd r).
Proof. exact (SYM (@lem1308025 r h1)). Qed.
Lemma lem1308027 (r : nat -> nat) (h1 : ((term7 r) = r) = (is_nadd r)) : ((term7 r) = r) = (is_nadd r).
Proof. exact (h1). Qed.
Lemma lem1308028 (r : nat -> nat) (h1 : ((term7 r) = r) = (is_nadd r)) : (is_nadd r) = ((term7 r) = r).
Proof. exact (SYM (@lem1308027 r h1)). Qed.
Lemma lem1308029 (r : nat -> nat) : ((is_nadd r) = ((term7 r) = r)) = (((term7 r) = r) = (is_nadd r)).
Proof. exact (prop_ext (fun h1 : (is_nadd r) = ((term7 r) = r) => @lem1308026 r h1) (fun h1 : ((term7 r) = r) = (is_nadd r) => @lem1308028 r h1)). Qed.
Lemma lem1308031 (x : nat -> nat) : term8 x.
Proof. exact (@lem1262615 x). Qed.
Lemma lem1308032 (x : nat -> nat) : (term8 x) = ((is_nadd x) = (term9 x)).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1308034 (x : nadd) : term10 x.
Proof. exact (@lem9784 (term11 x)). Qed.
Lemma lem1308035 (x : nadd) : (term10 x) = (term12 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1308036 (x : nadd) : term12 x.
Proof. exact (EQ_MP (@lem1308035 x) (@lem1308034 x)). Qed.
Lemma lem1308037 (x : nadd) (h1 : term11 x) : term11 x.
Proof. exact (h1). Qed.
Lemma lem1308038 (x : nadd) (h1 : term3 x) : term3 x.
Proof. exact (h1). Qed.
Lemma lem1308039 (x : nadd) : term13 x.
Proof. exact (@lem1308008 x). Qed.
Lemma lem1308040 (x : nadd) : (term13 x) = ((nadd_inv x) = (term14 x)).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1308045 (x : nadd) : (nadd_inv x) = (term14 x).
Proof. exact (EQ_MP (@lem1308040 x) (@lem1308039 x)). Qed.
Lemma lem1308046 : dest_nadd = dest_nadd.
Proof. exact (eq_refl dest_nadd). Qed.
Lemma lem1308047 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1308046) (@lem1308045 x)). Qed.
Lemma lem1308048 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem1308049 (x : nadd) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1308048) (@lem1308047 x)). Qed.
Lemma lem1308050 (x : nadd) : (term19 x) = (term19 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1308051 (x : nadd) : ((term15 x) = (term19 x)) = ((term16 x) = (term19 x)).
Proof. exact (MK_COMB (@lem1308049 x) (@lem1308050 x)). Qed.
Lemma lem1308054 (x : nadd) : ((term16 x) = (term19 x)) = ((term15 x) = (term19 x)).
Proof. exact (SYM (@lem1308051 x)). Qed.
Lemma lem1308085 : term20.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem1308086 (n : nat) : term21 n.
Proof. exact (@lem1308085 n). Qed.
Lemma lem1308087 (n : nat) : (term21 n) = ((term22 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem1308089 (k : nat) : term23 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1308090 (k : nat) : (term23 k) = ((term24 k) = (term25 k)).
Proof. exact (eq_refl (term23 k)). Qed.
Lemma lem1308092 (x : nadd) : (term11 x) = ((term11 x) = True).
Proof. exact (@lem7 (term11 x)). Qed.
Lemma lem1308097 (x : nadd) (h1 : term11 x) : (term11 x) = True.
Proof. exact (EQ_MP (@lem1308092 x) (@lem1308037 x h1)). Qed.
Lemma lem1308098 : (@COND nadd) = (@COND nadd).
Proof. exact (eq_refl (@COND nadd)). Qed.
Lemma lem1308099 (x : nadd) (h1 : term11 x) : (term26 x) = (@COND nadd True).
Proof. exact (MK_COMB (@lem1308098) (@lem1308097 x h1)). Qed.
Lemma lem1308100 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem1308101 (x : nadd) (h1 : term11 x) : (term28 x) = term29.
Proof. exact (MK_COMB (@lem1308099 x h1) (@lem1308100)). Qed.
Lemma lem1308102 (x : nadd) : (term30 x) = (term30 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1308103 (x : nadd) (h1 : term11 x) : (term14 x) = (term31 x).
Proof. exact (MK_COMB (@lem1308101 x h1) (@lem1308102 x)). Qed.
Lemma lem1308105 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1308106 (t2 : nadd) (t1 : nadd) : (@COND nadd True t1 t2) = t1.
Proof. exact (@lem1308105 nadd t2 t1). Qed.
Lemma lem1308107 (x : nadd) : (term31 x) = term27.
Proof. exact (@lem1308106 (term30 x) term27). Qed.
Lemma lem1308108 (x : nadd) (h1 : term11 x) : (term14 x) = term27.
Proof. exact (TRANS (@lem1308103 x h1) (@lem1308107 x)). Qed.
Lemma lem1308109 : dest_nadd = dest_nadd.
Proof. exact (eq_refl dest_nadd). Qed.
Lemma lem1308110 (x : nadd) (h1 : term11 x) : (term16 x) = term32.
Proof. exact (MK_COMB (@lem1308109) (@lem1308108 x h1)). Qed.
Lemma lem1308112 (k : nat) : (term24 k) = (term25 k).
Proof. exact (EQ_MP (@lem1308090 k) (@lem1308089 k)). Qed.
Lemma lem1308113 : term32 = term33.
Proof. exact (@lem1308112 (NUMERAL 0)). Qed.
Lemma lem1308115 (n : nat) : (term22 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1308087 n) (@lem1308086 n)). Qed.
Lemma lem1308116 : term33 = term34.
Proof. exact (fun_ext (fun n : nat => @lem1308115 n)). Qed.
Lemma lem1308117 : term32 = term34.
Proof. exact (TRANS (@lem1308113) (@lem1308116)). Qed.
Lemma lem1308118 (x : nadd) (h1 : term11 x) : (term16 x) = term34.
Proof. exact (TRANS (@lem1308110 x h1) (@lem1308117)). Qed.
Lemma lem1308119 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem1308120 (x : nadd) (h1 : term11 x) : (term18 x) = term35.
Proof. exact (MK_COMB (@lem1308119) (@lem1308118 x h1)). Qed.
Lemma lem1308122 (x : nadd) (h1 : term11 x) : (term11 x) = True.
Proof. exact (EQ_MP (@lem1308092 x) (@lem1308037 x h1)). Qed.
Lemma lem1308123 : (@COND (nat -> nat)) = (@COND (nat -> nat)).
Proof. exact (eq_refl (@COND (nat -> nat))). Qed.
Lemma lem1308124 (x : nadd) (h1 : term11 x) : (term36 x) = (@COND (nat -> nat) True).
Proof. exact (MK_COMB (@lem1308123) (@lem1308122 x h1)). Qed.
Lemma lem1308125 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1308126 (x : nadd) (h1 : term11 x) : (term37 x) = term38.
Proof. exact (MK_COMB (@lem1308124 x h1) (@lem1308125)). Qed.
Lemma lem1308127 (x : nadd) : (nadd_rinv x) = (nadd_rinv x).
Proof. exact (eq_refl (nadd_rinv x)). Qed.
Lemma lem1308128 (x : nadd) (h1 : term11 x) : (term19 x) = (term39 x).
Proof. exact (MK_COMB (@lem1308126 x h1) (@lem1308127 x)). Qed.
Lemma lem1308130 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1308131 (t2 : nat -> nat) (t1 : nat -> nat) : (@COND (nat -> nat) True t1 t2) = t1.
Proof. exact (@lem1308130 (nat -> nat) t2 t1). Qed.
Lemma lem1308132 (x : nadd) : (term39 x) = term34.
Proof. exact (@lem1308131 (nadd_rinv x) term34). Qed.
Lemma lem1308133 (x : nadd) (h1 : term11 x) : (term19 x) = term34.
Proof. exact (TRANS (@lem1308128 x h1) (@lem1308132 x)). Qed.
Lemma lem1308134 (x : nadd) (h1 : term11 x) : ((term16 x) = (term19 x)) = (term34 = term34).
Proof. exact (MK_COMB (@lem1308120 x h1) (@lem1308133 x h1)). Qed.
Lemma lem1308136 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1308137 (x : nat -> nat) : (x = x) = True.
Proof. exact (@lem1308136 (nat -> nat) x). Qed.
Lemma lem1308138 : (term34 = term34) = True.
Proof. exact (@lem1308137 term34). Qed.
Lemma lem1308139 (x : nadd) (h1 : term11 x) : ((term16 x) = (term19 x)) = True.
Proof. exact (TRANS (@lem1308134 x h1) (@lem1308138)). Qed.
Lemma lem1308140 (x : nadd) (h1 : term11 x) : True = ((term16 x) = (term19 x)).
Proof. exact (SYM (@lem1308139 x h1)). Qed.
Lemma lem1308141 (x : nadd) (h1 : term11 x) : (term16 x) = (term19 x).
Proof. exact (EQ_MP (@lem1308140 x h1) (@lem0)). Qed.
Lemma lem1308179 (x : nadd) : term40 x.
Proof. exact (@lem82 (term11 x)). Qed.
Lemma lem1308184 (x : nadd) (h1 : term3 x) : (term11 x) = False.
Proof. exact (@lem1308179 x (@lem1308038 x h1)). Qed.
Lemma lem1308185 : (@COND nadd) = (@COND nadd).
Proof. exact (eq_refl (@COND nadd)). Qed.
Lemma lem1308186 (x : nadd) (h1 : term3 x) : (term26 x) = (@COND nadd False).
Proof. exact (MK_COMB (@lem1308185) (@lem1308184 x h1)). Qed.
Lemma lem1308187 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem1308188 (x : nadd) (h1 : term3 x) : (term28 x) = term41.
Proof. exact (MK_COMB (@lem1308186 x h1) (@lem1308187)). Qed.
Lemma lem1308189 (x : nadd) : (term30 x) = (term30 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1308190 (x : nadd) (h1 : term3 x) : (term14 x) = (term42 x).
Proof. exact (MK_COMB (@lem1308188 x h1) (@lem1308189 x)). Qed.
Lemma lem1308192 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1308193 (t1 : nadd) (t2 : nadd) : (@COND nadd False t1 t2) = t2.
Proof. exact (@lem1308192 nadd t1 t2). Qed.
Lemma lem1308194 (x : nadd) : (term42 x) = (term30 x).
Proof. exact (@lem1308193 term27 (term30 x)). Qed.
Lemma lem1308195 (x : nadd) (h1 : term3 x) : (term14 x) = (term30 x).
Proof. exact (TRANS (@lem1308190 x h1) (@lem1308194 x)). Qed.
Lemma lem1308196 : dest_nadd = dest_nadd.
Proof. exact (eq_refl dest_nadd). Qed.
Lemma lem1308197 (x : nadd) (h1 : term3 x) : (term16 x) = (term43 x).
Proof. exact (MK_COMB (@lem1308196) (@lem1308195 x h1)). Qed.
Lemma lem1308198 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem1308199 (x : nadd) (h1 : term3 x) : (term18 x) = (term44 x).
Proof. exact (MK_COMB (@lem1308198) (@lem1308197 x h1)). Qed.
Lemma lem1308201 (x : nadd) (h1 : term3 x) : (term11 x) = False.
Proof. exact (@lem1308179 x (@lem1308038 x h1)). Qed.
Lemma lem1308202 : (@COND (nat -> nat)) = (@COND (nat -> nat)).
Proof. exact (eq_refl (@COND (nat -> nat))). Qed.
Lemma lem1308203 (x : nadd) (h1 : term3 x) : (term36 x) = (@COND (nat -> nat) False).
Proof. exact (MK_COMB (@lem1308202) (@lem1308201 x h1)). Qed.
Lemma lem1308204 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1308205 (x : nadd) (h1 : term3 x) : (term37 x) = term45.
Proof. exact (MK_COMB (@lem1308203 x h1) (@lem1308204)). Qed.
Lemma lem1308206 (x : nadd) : (nadd_rinv x) = (nadd_rinv x).
Proof. exact (eq_refl (nadd_rinv x)). Qed.
Lemma lem1308207 (x : nadd) (h1 : term3 x) : (term19 x) = (term46 x).
Proof. exact (MK_COMB (@lem1308205 x h1) (@lem1308206 x)). Qed.
Lemma lem1308209 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1308210 (t1 : nat -> nat) (t2 : nat -> nat) : (@COND (nat -> nat) False t1 t2) = t2.
Proof. exact (@lem1308209 (nat -> nat) t1 t2). Qed.
Lemma lem1308211 (x : nadd) : (term46 x) = (nadd_rinv x).
Proof. exact (@lem1308210 term34 (nadd_rinv x)). Qed.
Lemma lem1308212 (x : nadd) (h1 : term3 x) : (term19 x) = (nadd_rinv x).
Proof. exact (TRANS (@lem1308207 x h1) (@lem1308211 x)). Qed.
Lemma lem1308213 (x : nadd) (h1 : term3 x) : ((term16 x) = (term19 x)) = ((term43 x) = (nadd_rinv x)).
Proof. exact (MK_COMB (@lem1308199 x h1) (@lem1308212 x h1)). Qed.
Lemma lem1308216 (x : nadd) (h1 : term3 x) : ((term43 x) = (nadd_rinv x)) = ((term16 x) = (term19 x)).
Proof. exact (SYM (@lem1308213 x h1)). Qed.
Lemma lem1308218 (r : nat -> nat) : ((term7 r) = r) = (is_nadd r).
Proof. exact (EQ_MP (@lem1308029 r) (@lem1262760 r)). Qed.
Lemma lem1308219 (x : nadd) : ((term43 x) = (nadd_rinv x)) = (term47 x).
Proof. exact (@lem1308218 (nadd_rinv x)). Qed.
Lemma lem1308221 (x : nat -> nat) : (is_nadd x) = (term9 x).
Proof. exact (EQ_MP (@lem1308032 x) (@lem1308031 x)). Qed.
Lemma lem1308222 (x : nadd) : (term47 x) = (term4 x).
Proof. exact (@lem1308221 (nadd_rinv x)). Qed.
Lemma lem1308227 (x : nadd) : ((term43 x) = (nadd_rinv x)) = (term4 x).
Proof. exact (TRANS (@lem1308219 x) (@lem1308222 x)). Qed.
Lemma lem1308236 (x : nadd) : (term4 x) = ((term43 x) = (nadd_rinv x)).
Proof. exact (SYM (@lem1308227 x)). Qed.
Lemma lem1308238 (x : nadd) : term2 x.
Proof. exact (EQ_MP (@lem1308023 x) (@lem1308022 x)). Qed.
Lemma lem1308239 (x : nadd) (h1 : term3 x) : term4 x.
Proof. exact (@lem1308238 x (@lem1308038 x h1)). Qed.
Lemma lem1308240 (x : nadd) (h1 : term3 x) : (term43 x) = (nadd_rinv x).
Proof. exact (EQ_MP (@lem1308236 x) (@lem1308239 x h1)). Qed.
Lemma lem1308241 (x : nadd) (h1 : term3 x) : (term16 x) = (term19 x).
Proof. exact (EQ_MP (@lem1308216 x h1) (@lem1308240 x h1)). Qed.
Lemma lem1308242 (x : nadd) : (term16 x) = (term19 x).
Proof. exact (or_elim (@lem1308036 x) (fun h0 : term11 x => @lem1308141 x h0) (fun h0 : term3 x => @lem1308241 x h0)). Qed.
Lemma lem1308243 (x : nadd) : (term15 x) = (term19 x).
Proof. exact (EQ_MP (@lem1308054 x) (@lem1308242 x)). Qed.
Lemma lem1308248 : term48.
Proof. exact (fun x : nadd => @lem1308243 x). Qed.
