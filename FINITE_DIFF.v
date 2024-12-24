Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_DIFF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import SUBSET_DIFF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem3734145 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3734146 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3734147 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3734146 t1) (@lem3734145 t1)). Qed.
Lemma lem3734148 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3734147 t1 t2). Qed.
Lemma lem3734149 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3734150 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3734149 t1 t2) (@lem3734148 t1 t2)). Qed.
Lemma lem3734151 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3734150 t1 t2 t3). Qed.
Lemma lem3734152 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3734153 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3734152 t1 t2 t3) (@lem3734151 t1 t2 t3)). Qed.
Lemma lem3734154 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3734153 t1 t2 t3)). Qed.
Lemma lem3734156 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3734157 {_97970 : Type'} : (term8 _97970) = (term9 _97970).
Proof. exact (@lem3734156 (term8 _97970)). Qed.
Lemma lem3734158 {_97970 : Type'} : (term9 _97970) = (term8 _97970).
Proof. exact (SYM (@lem3734157 _97970)). Qed.
Lemma lem3734159 {_97970 : Type'} (h1 : term10 _97970) : term10 _97970.
Proof. exact (h1). Qed.
Lemma lem3734160 {_97970 : Type'} : term11 _97970.
Proof. exact (@lem3599924 _97970). Qed.
Lemma lem3734161 {_97970 : Type'} : term12 _97970.
Proof. exact (@lem3270702 _97970). Qed.
Lemma lem3734165 {_97970 : Type'} (h1 : term13 _97970) : term13 _97970.
Proof. exact (h1). Qed.
Lemma lem3734166 {_97970 : Type'} : term14 _97970.
Proof. exact (fun h0 : term13 _97970 => @lem3734165 _97970 h0). Qed.
Lemma lem3734167 {_97970 : Type'} (h1 : term14 _97970) : term14 _97970.
Proof. exact (h1). Qed.
Lemma lem3734168 {_97970 : Type'} (h1 : term13 _97970) : term13 _97970.
Proof. exact (h1). Qed.
Lemma lem3734169 {_97970 : Type'} (h1 : term13 _97970) (h2 : term14 _97970) : term13 _97970.
Proof. exact (@lem3734167 _97970 h2 (@lem3734168 _97970 h1)). Qed.
Lemma lem3734170 {_97970 : Type'} (h1 : term13 _97970) : term15 _97970.
Proof. exact (fun h0 : term14 _97970 => @lem3734169 _97970 h1 h0). Qed.
Lemma lem3734171 {_97970 : Type'} (h1 : term14 _97970) : term14 _97970.
Proof. exact (h1). Qed.
Lemma lem3734172 {_97970 : Type'} (h1 : term13 _97970) (h2 : term14 _97970) : term13 _97970.
Proof. exact (@lem3734170 _97970 h1 (@lem3734171 _97970 h2)). Qed.
Lemma lem3734173 {_97970 : Type'} (h1 : term14 _97970) : term14 _97970.
Proof. exact (fun h0 : term13 _97970 => @lem3734172 _97970 h0 h1). Qed.
Lemma lem3734174 {_97970 : Type'} : term16 _97970.
Proof. exact (fun h0 : term14 _97970 => @lem3734173 _97970 h0). Qed.
Lemma lem3734177 {_97970 : Type'} : term14 _97970.
Proof. exact (@lem3734174 _97970 (@lem3734166 _97970)). Qed.
Lemma lem3734178 {_97970 : Type'} : term14 _97970.
Proof. exact (@lem3734177 _97970). Qed.
Lemma lem3734202 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3734203 {_97970 : Type'} : (term17 _97970) = (term18 _97970).
Proof. exact (@lem3734202 (term11 _97970)). Qed.
Lemma lem3734216 {_97970 : Type'} : (term19 _97970) = (term19 _97970).
Proof. exact (eq_refl (term19 _97970)). Qed.
Lemma lem3734217 {_97970 : Type'} : (term20 _97970) = (term21 _97970).
Proof. exact (MK_COMB (@lem3734216 _97970) (@lem3734203 _97970)). Qed.
Lemma lem3734220 {_97970 : Type'} : (term22 _97970) = (term22 _97970).
Proof. exact (eq_refl (term22 _97970)). Qed.
Lemma lem3734227 {_97970 : Type'} : (term13 _97970) = (term23 _97970).
Proof. exact (MK_COMB (@lem3734220 _97970) (@lem3734217 _97970)). Qed.
Lemma lem3734236 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term24 _97970 t s) = (term24 _97970 t s).
Proof. exact (eq_refl (term24 _97970 t s)). Qed.
Lemma lem3734237 {_97970 : Type'} (s : _97970 -> Prop) : (term25 _97970 s) = (term25 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734236 _97970 t s)). Qed.
Lemma lem3734238 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734239 {_97970 : Type'} (s : _97970 -> Prop) : (term26 _97970 s) = (term26 _97970 s).
Proof. exact (MK_COMB (@lem3734238 _97970) (@lem3734237 _97970 s)). Qed.
Lemma lem3734240 {_97970 : Type'} : (term27 _97970) = (term27 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734239 _97970 s)). Qed.
Lemma lem3734241 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734242 {_97970 : Type'} : (term11 _97970) = (term11 _97970).
Proof. exact (MK_COMB (@lem3734241 _97970) (@lem3734240 _97970)). Qed.
Lemma lem3734243 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3734244 {_97970 : Type'} : (term18 _97970) = (term18 _97970).
Proof. exact (MK_COMB (@lem3734243) (@lem3734242 _97970)). Qed.
Lemma lem3734245 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term28 _97970 t s) = (term28 _97970 t s).
Proof. exact (eq_refl (term28 _97970 t s)). Qed.
Lemma lem3734246 {_97970 : Type'} (s : _97970 -> Prop) : (term29 _97970 s) = (term29 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734245 _97970 t s)). Qed.
Lemma lem3734247 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734248 {_97970 : Type'} (s : _97970 -> Prop) : (term30 _97970 s) = (term30 _97970 s).
Proof. exact (MK_COMB (@lem3734247 _97970) (@lem3734246 _97970 s)). Qed.
Lemma lem3734249 {_97970 : Type'} : (term31 _97970) = (term31 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734248 _97970 s)). Qed.
Lemma lem3734250 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734251 {_97970 : Type'} : (term12 _97970) = (term12 _97970).
Proof. exact (MK_COMB (@lem3734250 _97970) (@lem3734249 _97970)). Qed.
Lemma lem3734252 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3734253 {_97970 : Type'} : (term19 _97970) = (term19 _97970).
Proof. exact (MK_COMB (@lem3734252) (@lem3734251 _97970)). Qed.
Lemma lem3734254 {_97970 : Type'} : (term21 _97970) = (term21 _97970).
Proof. exact (MK_COMB (@lem3734253 _97970) (@lem3734244 _97970)). Qed.
Lemma lem3734259 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term32 _97970 s t) = (term32 _97970 s t).
Proof. exact (eq_refl (term32 _97970 s t)). Qed.
Lemma lem3734260 {_97970 : Type'} (s : _97970 -> Prop) : (term33 _97970 s) = (term33 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734259 _97970 s t)). Qed.
Lemma lem3734261 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734262 {_97970 : Type'} (s : _97970 -> Prop) : (term34 _97970 s) = (term34 _97970 s).
Proof. exact (MK_COMB (@lem3734261 _97970) (@lem3734260 _97970 s)). Qed.
Lemma lem3734263 {_97970 : Type'} : (term35 _97970) = (term35 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734262 _97970 s)). Qed.
Lemma lem3734264 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734265 {_97970 : Type'} : (term8 _97970) = (term8 _97970).
Proof. exact (MK_COMB (@lem3734264 _97970) (@lem3734263 _97970)). Qed.
Lemma lem3734266 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3734267 {_97970 : Type'} : (term10 _97970) = (term10 _97970).
Proof. exact (MK_COMB (@lem3734266) (@lem3734265 _97970)). Qed.
Lemma lem3734268 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3734269 {_97970 : Type'} : (term22 _97970) = (term22 _97970).
Proof. exact (MK_COMB (@lem3734268) (@lem3734267 _97970)). Qed.
Lemma lem3734270 {_97970 : Type'} : (term23 _97970) = (term23 _97970).
Proof. exact (MK_COMB (@lem3734269 _97970) (@lem3734254 _97970)). Qed.
Lemma lem3734319 {_97970 : Type'} : (term13 _97970) = (term23 _97970).
Proof. exact (TRANS (@lem3734227 _97970) (@lem3734270 _97970)). Qed.
Lemma lem3734320 {_97970 : Type'} : (term23 _97970) = (term13 _97970).
Proof. exact (SYM (@lem3734319 _97970)). Qed.
Lemma lem3734321 {_97970 : Type'} (h1 : term10 _97970) : term10 _97970.
Proof. exact (h1). Qed.
Lemma lem3734322 {_97970 : Type'} (h1 : term12 _97970) : term12 _97970.
Proof. exact (h1). Qed.
Lemma lem3734323 {_97970 : Type'} (h1 : term11 _97970) : term11 _97970.
Proof. exact (h1). Qed.
Lemma lem3734330 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term36 _97970 s t) = (term37 _97970 s t).
Proof. exact (@lem17362 (@FINITE _97970 s) (term38 _97970 s t)). Qed.
Lemma lem3734331 {_97970 : Type'} (P : type686 _97970) : (term39 _97970 P) = (term40 _97970 P).
Proof. exact (@lem18392 (_97970 -> Prop) P). Qed.
Lemma lem3734332 {_97970 : Type'} (s : _97970 -> Prop) : (term41 _97970 s) = (term42 _97970 s).
Proof. exact (@lem3734331 _97970 (term33 _97970 s)). Qed.
Lemma lem3734333 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term43 _97970 s t) = (term32 _97970 s t).
Proof. exact (eq_refl (term43 _97970 s t)). Qed.
Lemma lem3734334 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3734335 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term44 _97970 s t) = (term36 _97970 s t).
Proof. exact (MK_COMB (@lem3734334) (@lem3734333 _97970 s t)). Qed.
Lemma lem3734336 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term44 _97970 s t) = (term37 _97970 s t).
Proof. exact (TRANS (@lem3734335 _97970 s t) (@lem3734330 _97970 s t)). Qed.
Lemma lem3734337 {_97970 : Type'} (s : _97970 -> Prop) : (term45 _97970 s) = (term46 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734336 _97970 s t)). Qed.
Lemma lem3734338 {_97970 : Type'} : (@ex (_97970 -> Prop)) = (@ex (_97970 -> Prop)).
Proof. exact (eq_refl (@ex (_97970 -> Prop))). Qed.
Lemma lem3734339 {_97970 : Type'} (s : _97970 -> Prop) : (term42 _97970 s) = (term47 _97970 s).
Proof. exact (MK_COMB (@lem3734338 _97970) (@lem3734337 _97970 s)). Qed.
Lemma lem3734340 {_97970 : Type'} (s : _97970 -> Prop) : (term41 _97970 s) = (term47 _97970 s).
Proof. exact (TRANS (@lem3734332 _97970 s) (@lem3734339 _97970 s)). Qed.
Lemma lem3734341 {_97970 : Type'} (P : type686 _97970) : (term39 _97970 P) = (term40 _97970 P).
Proof. exact (@lem18392 (_97970 -> Prop) P). Qed.
Lemma lem3734342 {_97970 : Type'} : (term10 _97970) = (term48 _97970).
Proof. exact (@lem3734341 _97970 (term35 _97970)). Qed.
Lemma lem3734343 {_97970 : Type'} (s : _97970 -> Prop) : (term49 _97970 s) = (term34 _97970 s).
Proof. exact (eq_refl (term49 _97970 s)). Qed.
Lemma lem3734344 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3734345 {_97970 : Type'} (s : _97970 -> Prop) : (term50 _97970 s) = (term41 _97970 s).
Proof. exact (MK_COMB (@lem3734344) (@lem3734343 _97970 s)). Qed.
Lemma lem3734346 {_97970 : Type'} (s : _97970 -> Prop) : (term50 _97970 s) = (term47 _97970 s).
Proof. exact (TRANS (@lem3734345 _97970 s) (@lem3734340 _97970 s)). Qed.
Lemma lem3734347 {_97970 : Type'} : (term51 _97970) = (term52 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734346 _97970 s)). Qed.
Lemma lem3734348 {_97970 : Type'} : (@ex (_97970 -> Prop)) = (@ex (_97970 -> Prop)).
Proof. exact (eq_refl (@ex (_97970 -> Prop))). Qed.
Lemma lem3734349 {_97970 : Type'} : (term48 _97970) = (term53 _97970).
Proof. exact (MK_COMB (@lem3734348 _97970) (@lem3734347 _97970)). Qed.
Lemma lem3734350 {_97970 : Type'} : (term10 _97970) = (term53 _97970).
Proof. exact (TRANS (@lem3734342 _97970) (@lem3734349 _97970)). Qed.
Lemma lem3734356 {A : Type'} (P : Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem3734357 {_97970 : Type'} (P : Prop) (Q : type686 _97970) : (term56 _97970 P Q) = (term57 _97970 P Q).
Proof. exact (@lem3734356 (_97970 -> Prop) P Q). Qed.
Lemma lem3734358 {_97970 : Type'} (s : _97970 -> Prop) : (term58 _97970 s) = (term59 _97970 s).
Proof. exact (@lem3734357 _97970 (@FINITE _97970 s) (term60 _97970 s)). Qed.
Lemma lem3734359 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term61 _97970 s t) = (term62 _97970 s t).
Proof. exact (eq_refl (term61 _97970 s t)). Qed.
Lemma lem3734360 {_97970 : Type'} (s : _97970 -> Prop) : (term63 _97970 s) = (term63 _97970 s).
Proof. exact (eq_refl (term63 _97970 s)). Qed.
Lemma lem3734361 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term64 _97970 s t) = (term37 _97970 s t).
Proof. exact (MK_COMB (@lem3734360 _97970 s) (@lem3734359 _97970 s t)). Qed.
Lemma lem3734362 {_97970 : Type'} (s : _97970 -> Prop) : (term65 _97970 s) = (term46 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734361 _97970 s t)). Qed.
Lemma lem3734363 {_97970 : Type'} : (@ex (_97970 -> Prop)) = (@ex (_97970 -> Prop)).
Proof. exact (eq_refl (@ex (_97970 -> Prop))). Qed.
Lemma lem3734364 {_97970 : Type'} (s : _97970 -> Prop) : (term58 _97970 s) = (term47 _97970 s).
Proof. exact (MK_COMB (@lem3734363 _97970) (@lem3734362 _97970 s)). Qed.
Lemma lem3734365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3734366 {_97970 : Type'} (s : _97970 -> Prop) : (term66 _97970 s) = (term67 _97970 s).
Proof. exact (MK_COMB (@lem3734365) (@lem3734364 _97970 s)). Qed.
Lemma lem3734367 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term61 _97970 s t) = (term62 _97970 s t).
Proof. exact (eq_refl (term61 _97970 s t)). Qed.
Lemma lem3734368 {_97970 : Type'} (s : _97970 -> Prop) : (term68 _97970 s) = (term60 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734367 _97970 s t)). Qed.
Lemma lem3734369 {_97970 : Type'} : (@ex (_97970 -> Prop)) = (@ex (_97970 -> Prop)).
Proof. exact (eq_refl (@ex (_97970 -> Prop))). Qed.
Lemma lem3734370 {_97970 : Type'} (s : _97970 -> Prop) : (term69 _97970 s) = (term70 _97970 s).
Proof. exact (MK_COMB (@lem3734369 _97970) (@lem3734368 _97970 s)). Qed.
Lemma lem3734371 {_97970 : Type'} (s : _97970 -> Prop) : (term63 _97970 s) = (term63 _97970 s).
Proof. exact (eq_refl (term63 _97970 s)). Qed.
Lemma lem3734372 {_97970 : Type'} (s : _97970 -> Prop) : (term59 _97970 s) = (term71 _97970 s).
Proof. exact (MK_COMB (@lem3734371 _97970 s) (@lem3734370 _97970 s)). Qed.
Lemma lem3734373 {_97970 : Type'} (s : _97970 -> Prop) : ((term58 _97970 s) = (term59 _97970 s)) = ((term47 _97970 s) = (term71 _97970 s)).
Proof. exact (MK_COMB (@lem3734366 _97970 s) (@lem3734372 _97970 s)). Qed.
Lemma lem3734374 {_97970 : Type'} (s : _97970 -> Prop) : (term47 _97970 s) = (term71 _97970 s).
Proof. exact (EQ_MP (@lem3734373 _97970 s) (@lem3734358 _97970 s)). Qed.
Lemma lem3734379 {_97970 : Type'} : (term52 _97970) = (term72 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734374 _97970 s)). Qed.
Lemma lem3734380 {_97970 : Type'} : (@ex (_97970 -> Prop)) = (@ex (_97970 -> Prop)).
Proof. exact (eq_refl (@ex (_97970 -> Prop))). Qed.
Lemma lem3734381 {_97970 : Type'} : (term53 _97970) = (term73 _97970).
Proof. exact (MK_COMB (@lem3734380 _97970) (@lem3734379 _97970)). Qed.
Lemma lem3734411 {A : Type'} (P : Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3734412 {_97970 : Type'} (P : Prop) (Q : type686 _97970) : (term57 _97970 P Q) = (term56 _97970 P Q).
Proof. exact (@lem3734411 (_97970 -> Prop) P Q). Qed.
Lemma lem3734413 {_97970 : Type'} (s : _97970 -> Prop) : (term59 _97970 s) = (term58 _97970 s).
Proof. exact (@lem3734412 _97970 (@FINITE _97970 s) (term60 _97970 s)). Qed.
Lemma lem3734414 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term61 _97970 s t) = (term62 _97970 s t).
Proof. exact (eq_refl (term61 _97970 s t)). Qed.
Lemma lem3734415 {_97970 : Type'} (s : _97970 -> Prop) : (term68 _97970 s) = (term60 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734414 _97970 s t)). Qed.
Lemma lem3734416 {_97970 : Type'} : (@ex (_97970 -> Prop)) = (@ex (_97970 -> Prop)).
Proof. exact (eq_refl (@ex (_97970 -> Prop))). Qed.
Lemma lem3734417 {_97970 : Type'} (s : _97970 -> Prop) : (term69 _97970 s) = (term70 _97970 s).
Proof. exact (MK_COMB (@lem3734416 _97970) (@lem3734415 _97970 s)). Qed.
Lemma lem3734418 {_97970 : Type'} (s : _97970 -> Prop) : (term63 _97970 s) = (term63 _97970 s).
Proof. exact (eq_refl (term63 _97970 s)). Qed.
Lemma lem3734419 {_97970 : Type'} (s : _97970 -> Prop) : (term59 _97970 s) = (term71 _97970 s).
Proof. exact (MK_COMB (@lem3734418 _97970 s) (@lem3734417 _97970 s)). Qed.
Lemma lem3734420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3734421 {_97970 : Type'} (s : _97970 -> Prop) : (term74 _97970 s) = (term75 _97970 s).
Proof. exact (MK_COMB (@lem3734420) (@lem3734419 _97970 s)). Qed.
Lemma lem3734422 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term61 _97970 s t) = (term62 _97970 s t).
Proof. exact (eq_refl (term61 _97970 s t)). Qed.
Lemma lem3734423 {_97970 : Type'} (s : _97970 -> Prop) : (term63 _97970 s) = (term63 _97970 s).
Proof. exact (eq_refl (term63 _97970 s)). Qed.
Lemma lem3734424 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term64 _97970 s t) = (term37 _97970 s t).
Proof. exact (MK_COMB (@lem3734423 _97970 s) (@lem3734422 _97970 s t)). Qed.
Lemma lem3734425 {_97970 : Type'} (s : _97970 -> Prop) : (term65 _97970 s) = (term46 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734424 _97970 s t)). Qed.
Lemma lem3734426 {_97970 : Type'} : (@ex (_97970 -> Prop)) = (@ex (_97970 -> Prop)).
Proof. exact (eq_refl (@ex (_97970 -> Prop))). Qed.
Lemma lem3734427 {_97970 : Type'} (s : _97970 -> Prop) : (term58 _97970 s) = (term47 _97970 s).
Proof. exact (MK_COMB (@lem3734426 _97970) (@lem3734425 _97970 s)). Qed.
Lemma lem3734428 {_97970 : Type'} (s : _97970 -> Prop) : ((term59 _97970 s) = (term58 _97970 s)) = ((term71 _97970 s) = (term47 _97970 s)).
Proof. exact (MK_COMB (@lem3734421 _97970 s) (@lem3734427 _97970 s)). Qed.
Lemma lem3734429 {_97970 : Type'} (s : _97970 -> Prop) : (term71 _97970 s) = (term47 _97970 s).
Proof. exact (EQ_MP (@lem3734428 _97970 s) (@lem3734413 _97970 s)). Qed.
Lemma lem3734430 {_97970 : Type'} : (term72 _97970) = (term52 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734429 _97970 s)). Qed.
Lemma lem3734431 {_97970 : Type'} : (@ex (_97970 -> Prop)) = (@ex (_97970 -> Prop)).
Proof. exact (eq_refl (@ex (_97970 -> Prop))). Qed.
Lemma lem3734432 {_97970 : Type'} : (term73 _97970) = (term53 _97970).
Proof. exact (MK_COMB (@lem3734431 _97970) (@lem3734430 _97970)). Qed.
Lemma lem3734433 {_97970 : Type'} : (term53 _97970) = (term53 _97970).
Proof. exact (TRANS (@lem3734381 _97970) (@lem3734432 _97970)). Qed.
Lemma lem3734434 {_97970 : Type'} : (term10 _97970) = (term53 _97970).
Proof. exact (TRANS (@lem3734350 _97970) (@lem3734433 _97970)). Qed.
Lemma lem3734435 {_97970 : Type'} (h1 : term10 _97970) : term53 _97970.
Proof. exact (EQ_MP (@lem3734434 _97970) (@lem3734321 _97970 h1)). Qed.
Lemma lem3734436 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term28 _97970 t s) = (term28 _97970 t s).
Proof. exact (eq_refl (term28 _97970 t s)). Qed.
Lemma lem3734437 {_97970 : Type'} (s : _97970 -> Prop) : (term29 _97970 s) = (term29 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734436 _97970 t s)). Qed.
Lemma lem3734438 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734439 {_97970 : Type'} (s : _97970 -> Prop) : (term30 _97970 s) = (term30 _97970 s).
Proof. exact (MK_COMB (@lem3734438 _97970) (@lem3734437 _97970 s)). Qed.
Lemma lem3734440 {_97970 : Type'} : (term31 _97970) = (term31 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734439 _97970 s)). Qed.
Lemma lem3734441 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734454 {_97970 : Type'} : (term12 _97970) = (term12 _97970).
Proof. exact (MK_COMB (@lem3734441 _97970) (@lem3734440 _97970)). Qed.
Lemma lem3734455 {_97970 : Type'} (h1 : term12 _97970) : term12 _97970.
Proof. exact (EQ_MP (@lem3734454 _97970) (@lem3734322 _97970 h1)). Qed.
Lemma lem3734462 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term76 _97970 s t) = (term77 _97970 s t).
Proof. exact (@lem17045 (@FINITE _97970 t) (@SUBSET _97970 s t)). Qed.
Lemma lem3734463 {_97970 : Type'} (s : _97970 -> Prop) : (@FINITE _97970 s) = (@FINITE _97970 s).
Proof. exact (eq_refl (@FINITE _97970 s)). Qed.
Lemma lem3734464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3734465 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term78 _97970 s t) = (term79 _97970 s t).
Proof. exact (MK_COMB (@lem3734464) (@lem3734462 _97970 s t)). Qed.
Lemma lem3734466 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term80 _97970 t s) = (term81 _97970 t s).
Proof. exact (MK_COMB (@lem3734465 _97970 s t) (@lem3734463 _97970 s)). Qed.
Lemma lem3734467 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term24 _97970 t s) = (term80 _97970 t s).
Proof. exact (@lem17265 (term82 _97970 s t) (@FINITE _97970 s)). Qed.
Lemma lem3734468 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term24 _97970 t s) = (term81 _97970 t s).
Proof. exact (TRANS (@lem3734467 _97970 t s) (@lem3734466 _97970 t s)). Qed.
Lemma lem3734469 {_97970 : Type'} (s : _97970 -> Prop) : (term25 _97970 s) = (term83 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734468 _97970 t s)). Qed.
Lemma lem3734470 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734471 {_97970 : Type'} (s : _97970 -> Prop) : (term26 _97970 s) = (term84 _97970 s).
Proof. exact (MK_COMB (@lem3734470 _97970) (@lem3734469 _97970 s)). Qed.
Lemma lem3734472 {_97970 : Type'} : (term27 _97970) = (term85 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734471 _97970 s)). Qed.
Lemma lem3734473 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734474 {_97970 : Type'} : (term11 _97970) = (term86 _97970).
Proof. exact (MK_COMB (@lem3734473 _97970) (@lem3734472 _97970)). Qed.
Lemma lem3734500 {A : Type'} (P : A -> Prop) (Q : Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem3734501 {_97970 : Type'} (P : type686 _97970) (Q : Prop) : (term89 _97970 P Q) = (term90 _97970 P Q).
Proof. exact (@lem3734500 (_97970 -> Prop) P Q). Qed.
Lemma lem3734502 {_97970 : Type'} (s : _97970 -> Prop) : (term91 _97970 s) = (term92 _97970 s).
Proof. exact (@lem3734501 _97970 (term93 _97970 s) (@FINITE _97970 s)). Qed.
Lemma lem3734503 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term94 _97970 s t) = (term77 _97970 s t).
Proof. exact (eq_refl (term94 _97970 s t)). Qed.
Lemma lem3734504 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3734505 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term95 _97970 s t) = (term79 _97970 s t).
Proof. exact (MK_COMB (@lem3734504) (@lem3734503 _97970 s t)). Qed.
Lemma lem3734506 {_97970 : Type'} (s : _97970 -> Prop) : (@FINITE _97970 s) = (@FINITE _97970 s).
Proof. exact (eq_refl (@FINITE _97970 s)). Qed.
Lemma lem3734507 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term96 _97970 t s) = (term81 _97970 t s).
Proof. exact (MK_COMB (@lem3734505 _97970 s t) (@lem3734506 _97970 s)). Qed.
Lemma lem3734508 {_97970 : Type'} (s : _97970 -> Prop) : (term97 _97970 s) = (term83 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734507 _97970 t s)). Qed.
Lemma lem3734509 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734510 {_97970 : Type'} (s : _97970 -> Prop) : (term91 _97970 s) = (term84 _97970 s).
Proof. exact (MK_COMB (@lem3734509 _97970) (@lem3734508 _97970 s)). Qed.
Lemma lem3734511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3734512 {_97970 : Type'} (s : _97970 -> Prop) : (term98 _97970 s) = (term99 _97970 s).
Proof. exact (MK_COMB (@lem3734511) (@lem3734510 _97970 s)). Qed.
Lemma lem3734513 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term94 _97970 s t) = (term77 _97970 s t).
Proof. exact (eq_refl (term94 _97970 s t)). Qed.
Lemma lem3734514 {_97970 : Type'} (s : _97970 -> Prop) : (term100 _97970 s) = (term93 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734513 _97970 s t)). Qed.
Lemma lem3734515 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734516 {_97970 : Type'} (s : _97970 -> Prop) : (term101 _97970 s) = (term102 _97970 s).
Proof. exact (MK_COMB (@lem3734515 _97970) (@lem3734514 _97970 s)). Qed.
Lemma lem3734517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3734518 {_97970 : Type'} (s : _97970 -> Prop) : (term103 _97970 s) = (term104 _97970 s).
Proof. exact (MK_COMB (@lem3734517) (@lem3734516 _97970 s)). Qed.
Lemma lem3734519 {_97970 : Type'} (s : _97970 -> Prop) : (@FINITE _97970 s) = (@FINITE _97970 s).
Proof. exact (eq_refl (@FINITE _97970 s)). Qed.
Lemma lem3734520 {_97970 : Type'} (s : _97970 -> Prop) : (term92 _97970 s) = (term105 _97970 s).
Proof. exact (MK_COMB (@lem3734518 _97970 s) (@lem3734519 _97970 s)). Qed.
Lemma lem3734521 {_97970 : Type'} (s : _97970 -> Prop) : ((term91 _97970 s) = (term92 _97970 s)) = ((term84 _97970 s) = (term105 _97970 s)).
Proof. exact (MK_COMB (@lem3734512 _97970 s) (@lem3734520 _97970 s)). Qed.
Lemma lem3734522 {_97970 : Type'} (s : _97970 -> Prop) : (term84 _97970 s) = (term105 _97970 s).
Proof. exact (EQ_MP (@lem3734521 _97970 s) (@lem3734502 _97970 s)). Qed.
Lemma lem3734571 {_97970 : Type'} : (term85 _97970) = (term106 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734522 _97970 s)). Qed.
Lemma lem3734572 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734607 {_97970 : Type'} : (term86 _97970) = (term107 _97970).
Proof. exact (MK_COMB (@lem3734572 _97970) (@lem3734571 _97970)). Qed.
Lemma lem3734608 {_97970 : Type'} : (term11 _97970) = (term107 _97970).
Proof. exact (TRANS (@lem3734474 _97970) (@lem3734607 _97970)). Qed.
Lemma lem3734609 {_97970 : Type'} (h1 : term11 _97970) : term107 _97970.
Proof. exact (EQ_MP (@lem3734608 _97970) (@lem3734323 _97970 h1)). Qed.
Lemma lem3734610 {_97970 : Type'} (s : _97970 -> Prop) (h1 : term47 _97970 s) : term47 _97970 s.
Proof. exact (h1). Qed.
Lemma lem3734620 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term28 _97970 t s) = (term28 _97970 t s).
Proof. exact (eq_refl (term28 _97970 t s)). Qed.
Lemma lem3734621 {_97970 : Type'} (s : _97970 -> Prop) : (term29 _97970 s) = (term29 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734620 _97970 t s)). Qed.
Lemma lem3734622 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734623 {_97970 : Type'} (s : _97970 -> Prop) : (term30 _97970 s) = (term30 _97970 s).
Proof. exact (MK_COMB (@lem3734622 _97970) (@lem3734621 _97970 s)). Qed.
Lemma lem3734624 {_97970 : Type'} : (term31 _97970) = (term31 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734623 _97970 s)). Qed.
Lemma lem3734625 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734626 {_97970 : Type'} : (term12 _97970) = (term12 _97970).
Proof. exact (MK_COMB (@lem3734625 _97970) (@lem3734624 _97970)). Qed.
Lemma lem3734627 {_97970 : Type'} (h1 : term12 _97970) : term12 _97970.
Proof. exact (EQ_MP (@lem3734626 _97970) (@lem3734455 _97970 h1)). Qed.
Lemma lem3734630 {_97970 : Type'} (s : _97970 -> Prop) : (@FINITE _97970 s) = (@FINITE _97970 s).
Proof. exact (eq_refl (@FINITE _97970 s)). Qed.
Lemma lem3734645 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term77 _97970 s t) = (term77 _97970 s t).
Proof. exact (eq_refl (term77 _97970 s t)). Qed.
Lemma lem3734646 {_97970 : Type'} (s : _97970 -> Prop) : (term93 _97970 s) = (term93 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734645 _97970 s t)). Qed.
Lemma lem3734647 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734648 {_97970 : Type'} (s : _97970 -> Prop) : (term102 _97970 s) = (term102 _97970 s).
Proof. exact (MK_COMB (@lem3734647 _97970) (@lem3734646 _97970 s)). Qed.
Lemma lem3734649 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3734650 {_97970 : Type'} (s : _97970 -> Prop) : (term104 _97970 s) = (term104 _97970 s).
Proof. exact (MK_COMB (@lem3734649) (@lem3734648 _97970 s)). Qed.
Lemma lem3734651 {_97970 : Type'} (s : _97970 -> Prop) : (term105 _97970 s) = (term105 _97970 s).
Proof. exact (MK_COMB (@lem3734650 _97970 s) (@lem3734630 _97970 s)). Qed.
Lemma lem3734652 {_97970 : Type'} : (term106 _97970) = (term106 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734651 _97970 s)). Qed.
Lemma lem3734653 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734654 {_97970 : Type'} : (term107 _97970) = (term107 _97970).
Proof. exact (MK_COMB (@lem3734653 _97970) (@lem3734652 _97970)). Qed.
Lemma lem3734655 {_97970 : Type'} (h1 : term11 _97970) : term107 _97970.
Proof. exact (EQ_MP (@lem3734654 _97970) (@lem3734609 _97970 h1)). Qed.
Lemma lem3734671 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term37 _97970 s t) : term37 _97970 s t.
Proof. exact (h1). Qed.
Lemma lem3734675 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term28 _97970 t s) = (term28 _97970 t s).
Proof. exact (eq_refl (term28 _97970 t s)). Qed.
Lemma lem3734676 {_97970 : Type'} (s : _97970 -> Prop) : (term29 _97970 s) = (term29 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734675 _97970 t s)). Qed.
Lemma lem3734677 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734678 {_97970 : Type'} (s : _97970 -> Prop) : (term30 _97970 s) = (term30 _97970 s).
Proof. exact (MK_COMB (@lem3734677 _97970) (@lem3734676 _97970 s)). Qed.
Lemma lem3734679 {_97970 : Type'} : (term31 _97970) = (term31 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734678 _97970 s)). Qed.
Lemma lem3734680 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734682 {_97970 : Type'} : (term12 _97970) = (term12 _97970).
Proof. exact (MK_COMB (@lem3734680 _97970) (@lem3734679 _97970)). Qed.
Lemma lem3734683 {_97970 : Type'} (h1 : term12 _97970) : term12 _97970.
Proof. exact (EQ_MP (@lem3734682 _97970) (@lem3734627 _97970 h1)). Qed.
Lemma lem3734685 {A : Type'} (P : A -> Prop) (Q : Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3734686 {_97970 : Type'} (P : type686 _97970) (Q : Prop) : (term90 _97970 P Q) = (term89 _97970 P Q).
Proof. exact (@lem3734685 (_97970 -> Prop) P Q). Qed.
Lemma lem3734687 {_97970 : Type'} (s : _97970 -> Prop) : (term92 _97970 s) = (term91 _97970 s).
Proof. exact (@lem3734686 _97970 (term93 _97970 s) (@FINITE _97970 s)). Qed.
Lemma lem3734688 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term94 _97970 s t) = (term77 _97970 s t).
Proof. exact (eq_refl (term94 _97970 s t)). Qed.
Lemma lem3734689 {_97970 : Type'} (s : _97970 -> Prop) : (term100 _97970 s) = (term93 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734688 _97970 s t)). Qed.
Lemma lem3734690 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734691 {_97970 : Type'} (s : _97970 -> Prop) : (term101 _97970 s) = (term102 _97970 s).
Proof. exact (MK_COMB (@lem3734690 _97970) (@lem3734689 _97970 s)). Qed.
Lemma lem3734692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3734693 {_97970 : Type'} (s : _97970 -> Prop) : (term103 _97970 s) = (term104 _97970 s).
Proof. exact (MK_COMB (@lem3734692) (@lem3734691 _97970 s)). Qed.
Lemma lem3734694 {_97970 : Type'} (s : _97970 -> Prop) : (@FINITE _97970 s) = (@FINITE _97970 s).
Proof. exact (eq_refl (@FINITE _97970 s)). Qed.
Lemma lem3734695 {_97970 : Type'} (s : _97970 -> Prop) : (term92 _97970 s) = (term105 _97970 s).
Proof. exact (MK_COMB (@lem3734693 _97970 s) (@lem3734694 _97970 s)). Qed.
Lemma lem3734696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3734697 {_97970 : Type'} (s : _97970 -> Prop) : (term108 _97970 s) = (term109 _97970 s).
Proof. exact (MK_COMB (@lem3734696) (@lem3734695 _97970 s)). Qed.
Lemma lem3734698 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term94 _97970 s t) = (term77 _97970 s t).
Proof. exact (eq_refl (term94 _97970 s t)). Qed.
Lemma lem3734699 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3734700 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term95 _97970 s t) = (term79 _97970 s t).
Proof. exact (MK_COMB (@lem3734699) (@lem3734698 _97970 s t)). Qed.
Lemma lem3734701 {_97970 : Type'} (s : _97970 -> Prop) : (@FINITE _97970 s) = (@FINITE _97970 s).
Proof. exact (eq_refl (@FINITE _97970 s)). Qed.
Lemma lem3734702 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term96 _97970 t s) = (term81 _97970 t s).
Proof. exact (MK_COMB (@lem3734700 _97970 s t) (@lem3734701 _97970 s)). Qed.
Lemma lem3734703 {_97970 : Type'} (s : _97970 -> Prop) : (term97 _97970 s) = (term83 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734702 _97970 t s)). Qed.
Lemma lem3734704 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734705 {_97970 : Type'} (s : _97970 -> Prop) : (term91 _97970 s) = (term84 _97970 s).
Proof. exact (MK_COMB (@lem3734704 _97970) (@lem3734703 _97970 s)). Qed.
Lemma lem3734706 {_97970 : Type'} (s : _97970 -> Prop) : ((term92 _97970 s) = (term91 _97970 s)) = ((term105 _97970 s) = (term84 _97970 s)).
Proof. exact (MK_COMB (@lem3734697 _97970 s) (@lem3734705 _97970 s)). Qed.
Lemma lem3734707 {_97970 : Type'} (s : _97970 -> Prop) : (term105 _97970 s) = (term84 _97970 s).
Proof. exact (EQ_MP (@lem3734706 _97970 s) (@lem3734687 _97970 s)). Qed.
Lemma lem3734708 {_97970 : Type'} : (term106 _97970) = (term85 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734707 _97970 s)). Qed.
Lemma lem3734709 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734710 {_97970 : Type'} : (term107 _97970) = (term86 _97970).
Proof. exact (MK_COMB (@lem3734709 _97970) (@lem3734708 _97970)). Qed.
Lemma lem3734723 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term81 _97970 t s) = (term81 _97970 t s).
Proof. exact (eq_refl (term81 _97970 t s)). Qed.
Lemma lem3734724 {_97970 : Type'} (s : _97970 -> Prop) : (term83 _97970 s) = (term83 _97970 s).
Proof. exact (fun_ext (fun t : _97970 -> Prop => @lem3734723 _97970 t s)). Qed.
Lemma lem3734725 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734726 {_97970 : Type'} (s : _97970 -> Prop) : (term84 _97970 s) = (term84 _97970 s).
Proof. exact (MK_COMB (@lem3734725 _97970) (@lem3734724 _97970 s)). Qed.
Lemma lem3734727 {_97970 : Type'} : (term85 _97970) = (term85 _97970).
Proof. exact (fun_ext (fun s : _97970 -> Prop => @lem3734726 _97970 s)). Qed.
Lemma lem3734728 {_97970 : Type'} : (@all (_97970 -> Prop)) = (@all (_97970 -> Prop)).
Proof. exact (eq_refl (@all (_97970 -> Prop))). Qed.
Lemma lem3734729 {_97970 : Type'} : (term86 _97970) = (term86 _97970).
Proof. exact (MK_COMB (@lem3734728 _97970) (@lem3734727 _97970)). Qed.
Lemma lem3734730 {_97970 : Type'} : (term107 _97970) = (term86 _97970).
Proof. exact (TRANS (@lem3734710 _97970) (@lem3734729 _97970)). Qed.
Lemma lem3734731 {_97970 : Type'} (h1 : term11 _97970) : term86 _97970.
Proof. exact (EQ_MP (@lem3734730 _97970) (@lem3734655 _97970 h1)). Qed.
Lemma lem3734740 {_97970 : Type'} (_42885 : _97970 -> Prop) (h1 : term12 _97970) : term110 _97970 _42885.
Proof. exact (@lem3734683 _97970 h1 _42885). Qed.
Lemma lem3734741 {_97970 : Type'} (_42885 : _97970 -> Prop) : (term110 _97970 _42885) = (term30 _97970 _42885).
Proof. exact (eq_refl (term110 _97970 _42885)). Qed.
Lemma lem3734742 {_97970 : Type'} (_42885 : _97970 -> Prop) (h1 : term12 _97970) : term30 _97970 _42885.
Proof. exact (EQ_MP (@lem3734741 _97970 _42885) (@lem3734740 _97970 _42885 h1)). Qed.
Lemma lem3734743 {_97970 : Type'} (_42885 : _97970 -> Prop) (_42886 : _97970 -> Prop) (h1 : term12 _97970) : term111 _97970 _42885 _42886.
Proof. exact (@lem3734742 _97970 _42885 h1 _42886). Qed.
Lemma lem3734744 {_97970 : Type'} (_42886 : _97970 -> Prop) (_42885 : _97970 -> Prop) : (term111 _97970 _42885 _42886) = (term28 _97970 _42886 _42885).
Proof. exact (eq_refl (term111 _97970 _42885 _42886)). Qed.
Lemma lem3734746 {_97970 : Type'} (_42887 : _97970 -> Prop) (h1 : term11 _97970) : term112 _97970 _42887.
Proof. exact (@lem3734731 _97970 h1 _42887). Qed.
Lemma lem3734747 {_97970 : Type'} (_42887 : _97970 -> Prop) : (term112 _97970 _42887) = (term84 _97970 _42887).
Proof. exact (eq_refl (term112 _97970 _42887)). Qed.
Lemma lem3734748 {_97970 : Type'} (_42887 : _97970 -> Prop) (h1 : term11 _97970) : term84 _97970 _42887.
Proof. exact (EQ_MP (@lem3734747 _97970 _42887) (@lem3734746 _97970 _42887 h1)). Qed.
Lemma lem3734749 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) (h1 : term11 _97970) : term113 _97970 _42887 _42888.
Proof. exact (@lem3734748 _97970 _42887 h1 _42888). Qed.
Lemma lem3734750 {_97970 : Type'} (_42888 : _97970 -> Prop) (_42887 : _97970 -> Prop) : (term113 _97970 _42887 _42888) = (term81 _97970 _42888 _42887).
Proof. exact (eq_refl (term113 _97970 _42887 _42888)). Qed.
Lemma lem3734751 {_97970 : Type'} (_42888 : _97970 -> Prop) (_42887 : _97970 -> Prop) (h1 : term11 _97970) : term81 _97970 _42888 _42887.
Proof. exact (EQ_MP (@lem3734750 _97970 _42888 _42887) (@lem3734749 _97970 _42887 _42888 h1)). Qed.
Lemma lem3734764 {_97970 : Type'} (_42888 : _97970 -> Prop) (_42887 : _97970 -> Prop) : (term81 _97970 _42888 _42887) = (term114 _97970 _42888 _42887).
Proof. exact (@lem3734154 (term115 _97970 _42888) (term116 _97970 _42887 _42888) (@FINITE _97970 _42887)). Qed.
Lemma lem3734765 {_97970 : Type'} (_42888 : _97970 -> Prop) (_42887 : _97970 -> Prop) (h1 : term11 _97970) : term114 _97970 _42888 _42887.
Proof. exact (EQ_MP (@lem3734764 _97970 _42888 _42887) (@lem3734751 _97970 _42888 _42887 h1)). Qed.
Lemma lem3734769 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term37 _97970 s t) : term62 _97970 s t.
Proof. exact (proj2 (@lem3734671 _97970 s t h1)). Qed.
Lemma lem3734771 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term37 _97970 s t) : @FINITE _97970 s.
Proof. exact (proj1 (@lem3734671 _97970 s t h1)). Qed.
Lemma lem3734772 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term37 _97970 s t) : term117 _97970 s.
Proof. exact (fun h0 : term115 _97970 s => @lem3734771 _97970 s t h1). Qed.
Lemma lem3734774 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3734775 {_97970 : Type'} (s : _97970 -> Prop) : (term117 _97970 s) = (@FINITE _97970 s).
Proof. exact (@lem3734774 (@FINITE _97970 s)). Qed.
Lemma lem3734776 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term37 _97970 s t) : @FINITE _97970 s.
Proof. exact (EQ_MP (@lem3734775 _97970 s) (@lem3734772 _97970 s t h1)). Qed.
Lemma lem3734778 {_97970 : Type'} (_42886 : _97970 -> Prop) (_42885 : _97970 -> Prop) (h1 : term12 _97970) : term28 _97970 _42886 _42885.
Proof. exact (EQ_MP (@lem3734744 _97970 _42886 _42885) (@lem3734743 _97970 _42885 _42886 h1)). Qed.
Lemma lem3734779 {_97970 : Type'} (_42886 : _97970 -> Prop) (_42885 : _97970 -> Prop) (h1 : term12 _97970) : term28 _97970 _42886 _42885.
Proof. exact (@lem3734778 _97970 _42886 _42885 h1). Qed.
Lemma lem3734780 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : term12 _97970) : term28 _97970 t s.
Proof. exact (@lem3734779 _97970 t s h1). Qed.
Lemma lem3734781 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : term12 _97970) : term119 _97970 t s.
Proof. exact (fun h0 : term120 _97970 t s => @lem3734780 _97970 t s h1). Qed.
Lemma lem3734783 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3734784 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) : (term119 _97970 t s) = (term28 _97970 t s).
Proof. exact (@lem3734783 (term28 _97970 t s)). Qed.
Lemma lem3734785 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : term12 _97970) : term28 _97970 t s.
Proof. exact (EQ_MP (@lem3734784 _97970 t s) (@lem3734781 _97970 t s h1)). Qed.
Lemma lem3734801 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3734802 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term121 _97970 _42888 _42887) = (term122 _97970 _42887 _42888).
Proof. exact (@lem3734801 (@FINITE _97970 _42887) (term116 _97970 _42887 _42888)). Qed.
Lemma lem3734808 {_97970 : Type'} (_42888 : _97970 -> Prop) : (term123 _97970 _42888) = (term123 _97970 _42888).
Proof. exact (eq_refl (term123 _97970 _42888)). Qed.
Lemma lem3734809 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term114 _97970 _42888 _42887) = (term124 _97970 _42887 _42888).
Proof. exact (MK_COMB (@lem3734808 _97970 _42888) (@lem3734802 _97970 _42887 _42888)). Qed.
Lemma lem3734813 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3734814 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term124 _97970 _42887 _42888) = (term125 _97970 _42887 _42888).
Proof. exact (@lem3734813 (@FINITE _97970 _42887) (term115 _97970 _42888) (term116 _97970 _42887 _42888)). Qed.
Lemma lem3734830 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term114 _97970 _42888 _42887) = (term125 _97970 _42887 _42888).
Proof. exact (TRANS (@lem3734809 _97970 _42887 _42888) (@lem3734814 _97970 _42887 _42888)). Qed.
Lemma lem3734831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3734832 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term126 _97970 _42888 _42887) = (term127 _97970 _42887 _42888).
Proof. exact (MK_COMB (@lem3734831) (@lem3734830 _97970 _42887 _42888)). Qed.
Lemma lem3734848 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term125 _97970 _42887 _42888) = (term125 _97970 _42887 _42888).
Proof. exact (eq_refl (term125 _97970 _42887 _42888)). Qed.
Lemma lem3734849 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : ((term114 _97970 _42888 _42887) = (term125 _97970 _42887 _42888)) = ((term125 _97970 _42887 _42888) = (term125 _97970 _42887 _42888)).
Proof. exact (MK_COMB (@lem3734832 _97970 _42887 _42888) (@lem3734848 _97970 _42887 _42888)). Qed.
Lemma lem3734851 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3734852 (x : Prop) : (x = x) = True.
Proof. exact (@lem3734851 Prop x). Qed.
Lemma lem3734853 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : ((term125 _97970 _42887 _42888) = (term125 _97970 _42887 _42888)) = True.
Proof. exact (@lem3734852 (term125 _97970 _42887 _42888)). Qed.
Lemma lem3734854 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : ((term114 _97970 _42888 _42887) = (term125 _97970 _42887 _42888)) = True.
Proof. exact (TRANS (@lem3734849 _97970 _42887 _42888) (@lem3734853 _97970 _42887 _42888)). Qed.
Lemma lem3734855 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : True = ((term114 _97970 _42888 _42887) = (term125 _97970 _42887 _42888)).
Proof. exact (SYM (@lem3734854 _97970 _42887 _42888)). Qed.
Lemma lem3734856 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term114 _97970 _42888 _42887) = (term125 _97970 _42887 _42888).
Proof. exact (EQ_MP (@lem3734855 _97970 _42887 _42888) (@lem0)). Qed.
Lemma lem3734857 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) (h1 : term11 _97970) : term125 _97970 _42887 _42888.
Proof. exact (EQ_MP (@lem3734856 _97970 _42887 _42888) (@lem3734765 _97970 _42888 _42887 h1)). Qed.
Lemma lem3734859 (b : Prop) (a : Prop) : (a \/ b) = (term128 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3734860 {_97970 : Type'} (_42888 : _97970 -> Prop) (_42887 : _97970 -> Prop) : (term125 _97970 _42887 _42888) = (term129 _97970 _42888 _42887).
Proof. exact (@lem3734859 (term77 _97970 _42887 _42888) (@FINITE _97970 _42887)). Qed.
Lemma lem3734862 (a : Prop) (b : Prop) : (term130 a b) = (term131 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3734863 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term132 _97970 _42887 _42888) = (term133 _97970 _42887 _42888).
Proof. exact (@lem3734862 (term115 _97970 _42888) (term116 _97970 _42887 _42888)). Qed.
Lemma lem3734865 (a : Prop) : (term134 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3734866 {_97970 : Type'} (_42888 : _97970 -> Prop) : (term135 _97970 _42888) = (@FINITE _97970 _42888).
Proof. exact (@lem3734865 (@FINITE _97970 _42888)). Qed.
Lemma lem3734867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3734868 {_97970 : Type'} (_42888 : _97970 -> Prop) : (term136 _97970 _42888) = (term63 _97970 _42888).
Proof. exact (MK_COMB (@lem3734867) (@lem3734866 _97970 _42888)). Qed.
Lemma lem3734870 (a : Prop) : (term134 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3734871 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term137 _97970 _42887 _42888) = (@SUBSET _97970 _42887 _42888).
Proof. exact (@lem3734870 (@SUBSET _97970 _42887 _42888)). Qed.
Lemma lem3734872 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term133 _97970 _42887 _42888) = (term82 _97970 _42887 _42888).
Proof. exact (MK_COMB (@lem3734868 _97970 _42888) (@lem3734871 _97970 _42887 _42888)). Qed.
Lemma lem3734873 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term132 _97970 _42887 _42888) = (term82 _97970 _42887 _42888).
Proof. exact (TRANS (@lem3734863 _97970 _42887 _42888) (@lem3734872 _97970 _42887 _42888)). Qed.
Lemma lem3734874 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3734875 {_97970 : Type'} (_42887 : _97970 -> Prop) (_42888 : _97970 -> Prop) : (term138 _97970 _42887 _42888) = (term139 _97970 _42887 _42888).
Proof. exact (MK_COMB (@lem3734874) (@lem3734873 _97970 _42887 _42888)). Qed.
Lemma lem3734876 {_97970 : Type'} (_42887 : _97970 -> Prop) : (@FINITE _97970 _42887) = (@FINITE _97970 _42887).
Proof. exact (eq_refl (@FINITE _97970 _42887)). Qed.
Lemma lem3734877 {_97970 : Type'} (_42888 : _97970 -> Prop) (_42887 : _97970 -> Prop) : (term129 _97970 _42888 _42887) = (term24 _97970 _42888 _42887).
Proof. exact (MK_COMB (@lem3734875 _97970 _42887 _42888) (@lem3734876 _97970 _42887)). Qed.
Lemma lem3734878 {_97970 : Type'} (_42888 : _97970 -> Prop) (_42887 : _97970 -> Prop) : (term125 _97970 _42887 _42888) = (term24 _97970 _42888 _42887).
Proof. exact (TRANS (@lem3734860 _97970 _42888 _42887) (@lem3734877 _97970 _42888 _42887)). Qed.
Lemma lem3734880 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term12 _97970) (h2 : term37 _97970 s t) : term140 _97970 t s.
Proof. exact (conj (@lem3734776 _97970 s t h2) (@lem3734785 _97970 t s h1)). Qed.
Lemma lem3734882 {_97970 : Type'} (_42888 : _97970 -> Prop) (_42887 : _97970 -> Prop) (h1 : term11 _97970) : term24 _97970 _42888 _42887.
Proof. exact (EQ_MP (@lem3734878 _97970 _42888 _42887) (@lem3734857 _97970 _42887 _42888 h1)). Qed.
Lemma lem3734883 {_97970 : Type'} (_42888 : _97970 -> Prop) (_42887 : _97970 -> Prop) (h1 : term11 _97970) : term24 _97970 _42888 _42887.
Proof. exact (@lem3734882 _97970 _42888 _42887 h1). Qed.
Lemma lem3734884 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) : term141 _97970 s t.
Proof. exact (@lem3734883 _97970 s (@DIFF _97970 s t) h1). Qed.
Lemma lem3734887 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : term38 _97970 s t.
Proof. exact (@lem3734884 _97970 s t h1 (@lem3734880 _97970 s t h2 h3)). Qed.
Lemma lem3734888 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : term142 _97970 s t.
Proof. exact (fun h0 : term62 _97970 s t => @lem3734887 _97970 s t h1 h2 h3). Qed.
Lemma lem3734890 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3734891 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term142 _97970 s t) = (term38 _97970 s t).
Proof. exact (@lem3734890 (term38 _97970 s t)). Qed.
Lemma lem3734892 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : term38 _97970 s t.
Proof. exact (EQ_MP (@lem3734891 _97970 s t) (@lem3734888 _97970 s t h1 h2 h3)). Qed.
Lemma lem3734895 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3734897 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term62 _97970 s t) = (term143 _97970 s t).
Proof. exact (@lem3734895 (term38 _97970 s t)). Qed.
Lemma lem3734900 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term37 _97970 s t) : term143 _97970 s t.
Proof. exact (EQ_MP (@lem3734897 _97970 s t) (@lem3734769 _97970 s t h1)). Qed.
Lemma lem3734903 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : False.
Proof. exact (@lem3734900 _97970 s t h3 (@lem3734892 _97970 s t h1 h2 h3)). Qed.
Lemma lem3734904 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : term144.
Proof. exact (fun h0 : ~ False => @lem3734903 _97970 s t h1 h2 h3). Qed.
Lemma lem3734906 (p : Prop) : (term118 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3734907 : term144 = False.
Proof. exact (@lem3734906 False). Qed.
Lemma lem3734908 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : False.
Proof. exact (EQ_MP (@lem3734907) (@lem3734904 _97970 s t h1 h2 h3)). Qed.
Lemma lem3734909 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : (term12 _97970) = False.
Proof. exact (prop_ext (fun h4 : term12 _97970 => @lem3734908 _97970 s t h1 h2 h3) (fun h4 : False => @lem3734683 _97970 h2)). Qed.
Lemma lem3734910 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : False.
Proof. exact (EQ_MP (@lem3734909 _97970 s t h1 h2 h3) (@lem3734683 _97970 h2)). Qed.
Lemma lem3734911 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : (term37 _97970 s t) = False.
Proof. exact (prop_ext (fun h4 : term37 _97970 s t => @lem3734910 _97970 s t h1 h2 h3) (fun h4 : False => @lem3734671 _97970 s t h3)). Qed.
Lemma lem3734912 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : False.
Proof. exact (EQ_MP (@lem3734911 _97970 s t h1 h2 h3) (@lem3734671 _97970 s t h3)). Qed.
Lemma lem3734913 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : (term12 _97970) = False.
Proof. exact (prop_ext (fun h4 : term12 _97970 => @lem3734912 _97970 s t h1 h2 h3) (fun h4 : False => @lem3734627 _97970 h2)). Qed.
Lemma lem3734914 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term37 _97970 s t) : False.
Proof. exact (EQ_MP (@lem3734913 _97970 s t h1 h2 h3) (@lem3734627 _97970 h2)). Qed.
Lemma lem3734915 {_97970 : Type'} (s : _97970 -> Prop) (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term47 _97970 s) : False.
Proof. exact (ex_elim (@lem3734610 _97970 s h3) (fun t : _97970 -> Prop => fun h0 : term46 _97970 s t => @lem3734914 _97970 s t h1 h2 h0)). Qed.
Lemma lem3734916 {_97970 : Type'} (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term10 _97970) : False.
Proof. exact (ex_elim (@lem3734435 _97970 h3) (fun s : _97970 -> Prop => fun h0 : term52 _97970 s => @lem3734915 _97970 s h1 h2 h0)). Qed.
Lemma lem3734917 {_97970 : Type'} (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term10 _97970) : (term12 _97970) = False.
Proof. exact (prop_ext (fun h4 : term12 _97970 => @lem3734916 _97970 h1 h2 h3) (fun h4 : False => @lem3734455 _97970 h2)). Qed.
Lemma lem3734918 {_97970 : Type'} (h1 : term11 _97970) (h2 : term12 _97970) (h3 : term10 _97970) : False.
Proof. exact (EQ_MP (@lem3734917 _97970 h1 h2 h3) (@lem3734455 _97970 h2)). Qed.
Lemma lem3734919 {_97970 : Type'} (h1 : term12 _97970) (h2 : term10 _97970) : term17 _97970.
Proof. exact (fun h0 : term11 _97970 => @lem3734918 _97970 h0 h1 h2). Qed.
Lemma lem3734920 {_97970 : Type'} : (term17 _97970) = (term18 _97970).
Proof. exact (@lem69 (term11 _97970)). Qed.
Lemma lem3734921 {_97970 : Type'} (h1 : term12 _97970) (h2 : term10 _97970) : term18 _97970.
Proof. exact (EQ_MP (@lem3734920 _97970) (@lem3734919 _97970 h1 h2)). Qed.
Lemma lem3734922 {_97970 : Type'} (h1 : term10 _97970) : term21 _97970.
Proof. exact (fun h0 : term12 _97970 => @lem3734921 _97970 h0 h1). Qed.
Lemma lem3734923 {_97970 : Type'} : term23 _97970.
Proof. exact (fun h0 : term10 _97970 => @lem3734922 _97970 h0). Qed.
Lemma lem3734924 {_97970 : Type'} : term13 _97970.
Proof. exact (EQ_MP (@lem3734320 _97970) (@lem3734923 _97970)). Qed.
Lemma lem3734926 {_97970 : Type'} : term13 _97970.
Proof. exact (@lem3734178 _97970 (@lem3734924 _97970)). Qed.
Lemma lem3734927 {_97970 : Type'} (h1 : term10 _97970) : term20 _97970.
Proof. exact (@lem3734926 _97970 (@lem3734159 _97970 h1)). Qed.
Lemma lem3734928 {_97970 : Type'} (h1 : term10 _97970) : term17 _97970.
Proof. exact (@lem3734927 _97970 h1 (@lem3734161 _97970)). Qed.
Lemma lem3734929 {_97970 : Type'} (h1 : term10 _97970) : False.
Proof. exact (@lem3734928 _97970 h1 (@lem3734160 _97970)). Qed.
Lemma lem3734930 {_97970 : Type'} (h1 : term10 _97970) : (term10 _97970) = False.
Proof. exact (prop_ext (fun h2 : term10 _97970 => @lem3734929 _97970 h1) (fun h2 : False => @lem3734159 _97970 h1)). Qed.
Lemma lem3734931 {_97970 : Type'} (h1 : term10 _97970) : False.
Proof. exact (EQ_MP (@lem3734930 _97970 h1) (@lem3734159 _97970 h1)). Qed.
Lemma lem3734932 {_97970 : Type'} : term9 _97970.
Proof. exact (fun h0 : term10 _97970 => @lem3734931 _97970 h0). Qed.
Lemma lem3734933 {_97970 : Type'} : term8 _97970.
Proof. exact (EQ_MP (@lem3734158 _97970) (@lem3734932 _97970)). Qed.
