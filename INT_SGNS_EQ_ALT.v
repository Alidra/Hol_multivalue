Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGNS_EQ_ALT_term_abbrevs.
Require Import REAL_SGNS_EQ_ALT_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299924_spec.
Require Import thm2299925_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309137 (x : int) : term0 x.
Proof. exact (@lem1863601 (real_of_int x)). Qed.
Lemma lem2309138 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309139 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2309138 x) (@lem2309137 x)). Qed.
Lemma lem2309140 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2309139 x (real_of_int y)). Qed.
Lemma lem2309141 (x : int) (y : int) : (term2 x y) = (((term3 x) = (term3 y)) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2309142 (x : int) (y : int) : ((term3 x) = (term3 y)) = (term4 x y).
Proof. exact (EQ_MP (@lem2309141 x y) (@lem2309140 x y)). Qed.
Lemma lem2309144 (x : int) : (term3 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309145 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309146 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2309145) (@lem2309144 x)). Qed.
Lemma lem2309148 (x : int) : (term3 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309149 (y : int) : (term3 y) = (term5 y).
Proof. exact (@lem2309148 y). Qed.
Lemma lem2309150 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((term5 x) = (term5 y)).
Proof. exact (MK_COMB (@lem2309146 x) (@lem2309149 y)). Qed.
Lemma lem2309152 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309153 (x : int) (y : int) : ((term5 x) = (term5 y)) = ((int_sgn x) = (int_sgn y)).
Proof. exact (@lem2309152 (int_sgn x) (int_sgn y)). Qed.
Lemma lem2309154 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((int_sgn x) = (int_sgn y)).
Proof. exact (TRANS (@lem2309150 x y) (@lem2309153 x y)). Qed.
Lemma lem2309155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309156 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2309155) (@lem2309154 x y)). Qed.
Lemma lem2309158 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309159 : term11 = term12.
Proof. exact (@lem2309158 (NUMERAL 0)). Qed.
Lemma lem2309160 (x : int) : (term13 x) = (term13 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem2309161 (x : int) : ((real_of_int x) = term11) = ((real_of_int x) = term12).
Proof. exact (MK_COMB (@lem2309160 x) (@lem2309159)). Qed.
Lemma lem2309163 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309164 (x : int) : ((real_of_int x) = term12) = (x = term14).
Proof. exact (@lem2309163 x term14). Qed.
Lemma lem2309165 (x : int) : ((real_of_int x) = term11) = (x = term14).
Proof. exact (TRANS (@lem2309161 x) (@lem2309164 x)). Qed.
Lemma lem2309166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2309167 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2309166) (@lem2309165 x)). Qed.
Lemma lem2309169 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309170 : term11 = term12.
Proof. exact (@lem2309169 (NUMERAL 0)). Qed.
Lemma lem2309171 (y : int) : (term13 y) = (term13 y).
Proof. exact (eq_refl (term13 y)). Qed.
Lemma lem2309172 (y : int) : ((real_of_int y) = term11) = ((real_of_int y) = term12).
Proof. exact (MK_COMB (@lem2309171 y) (@lem2309170)). Qed.
Lemma lem2309174 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309175 (y : int) : ((real_of_int y) = term12) = (y = term14).
Proof. exact (@lem2309174 y term14). Qed.
Lemma lem2309176 (y : int) : ((real_of_int y) = term11) = (y = term14).
Proof. exact (TRANS (@lem2309172 y) (@lem2309175 y)). Qed.
Lemma lem2309177 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem2309167 x) (@lem2309176 y)). Qed.
Lemma lem2309178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2309179 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem2309178) (@lem2309177 x y)). Qed.
Lemma lem2309181 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309182 : term11 = term12.
Proof. exact (@lem2309181 (NUMERAL 0)). Qed.
Lemma lem2309183 (x : int) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem2309184 (x : int) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem2309183 x) (@lem2309182)). Qed.
Lemma lem2309186 (x : int) (y : int) : (term24 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2309187 (x : int) : (term23 x) = (term25 x).
Proof. exact (@lem2309186 x term14). Qed.
Lemma lem2309188 (x : int) : (term22 x) = (term25 x).
Proof. exact (TRANS (@lem2309184 x) (@lem2309187 x)). Qed.
Lemma lem2309189 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2309190 (x : int) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem2309189) (@lem2309188 x)). Qed.
Lemma lem2309192 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309193 : term11 = term12.
Proof. exact (@lem2309192 (NUMERAL 0)). Qed.
Lemma lem2309194 (y : int) : (term21 y) = (term21 y).
Proof. exact (eq_refl (term21 y)). Qed.
Lemma lem2309195 (y : int) : (term22 y) = (term23 y).
Proof. exact (MK_COMB (@lem2309194 y) (@lem2309193)). Qed.
Lemma lem2309197 (x : int) (y : int) : (term24 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2309198 (y : int) : (term23 y) = (term25 y).
Proof. exact (@lem2309197 y term14). Qed.
Lemma lem2309199 (y : int) : (term22 y) = (term25 y).
Proof. exact (TRANS (@lem2309195 y) (@lem2309198 y)). Qed.
Lemma lem2309200 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem2309190 x) (@lem2309199 y)). Qed.
Lemma lem2309201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2309202 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem2309201) (@lem2309200 x y)). Qed.
Lemma lem2309204 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309205 : term11 = term12.
Proof. exact (@lem2309204 (NUMERAL 0)). Qed.
Lemma lem2309206 (x : int) : (term32 x) = (term32 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem2309207 (x : int) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem2309206 x) (@lem2309205)). Qed.
Lemma lem2309209 (x : int) (y : int) : (term35 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309210 (x : int) : (term34 x) = (term36 x).
Proof. exact (@lem2309209 x term14). Qed.
Lemma lem2309211 (x : int) : (term33 x) = (term36 x).
Proof. exact (TRANS (@lem2309207 x) (@lem2309210 x)). Qed.
Lemma lem2309212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2309213 (x : int) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem2309212) (@lem2309211 x)). Qed.
Lemma lem2309215 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309216 : term11 = term12.
Proof. exact (@lem2309215 (NUMERAL 0)). Qed.
Lemma lem2309217 (y : int) : (term32 y) = (term32 y).
Proof. exact (eq_refl (term32 y)). Qed.
Lemma lem2309218 (y : int) : (term33 y) = (term34 y).
Proof. exact (MK_COMB (@lem2309217 y) (@lem2309216)). Qed.
Lemma lem2309220 (x : int) (y : int) : (term35 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309221 (y : int) : (term34 y) = (term36 y).
Proof. exact (@lem2309220 y term14). Qed.
Lemma lem2309222 (y : int) : (term33 y) = (term36 y).
Proof. exact (TRANS (@lem2309218 y) (@lem2309221 y)). Qed.
Lemma lem2309223 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem2309213 x) (@lem2309222 y)). Qed.
Lemma lem2309224 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem2309202 x y) (@lem2309223 x y)). Qed.
Lemma lem2309225 (x : int) (y : int) : (term4 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem2309179 x y) (@lem2309224 x y)). Qed.
Lemma lem2309226 (x : int) (y : int) : (((term3 x) = (term3 y)) = (term4 x y)) = (((int_sgn x) = (int_sgn y)) = (term43 x y)).
Proof. exact (MK_COMB (@lem2309156 x y) (@lem2309225 x y)). Qed.
Lemma lem2309227 (x : int) (y : int) : ((int_sgn x) = (int_sgn y)) = (term43 x y).
Proof. exact (EQ_MP (@lem2309226 x y) (@lem2309142 x y)). Qed.
Lemma lem2309228 (x : int) : term44 x.
Proof. exact (fun y : int => @lem2309227 x y). Qed.
Lemma lem2309229 : term45.
Proof. exact (fun x : int => @lem2309228 x). Qed.
