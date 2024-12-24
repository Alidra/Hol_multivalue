Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NULL_term_abbrevs.
Require Import thm1099685_spec.
Require Import thm1100049_spec.
Lemma lem1100050 {_25287 : Type'} : (term0 _25287) = (term1 _25287).
Proof. exact (eq_refl (term0 _25287)). Qed.
Lemma lem1100051 {_25287 : Type'} : term1 _25287.
Proof. exact (EQ_MP (@lem1100050 _25287) (@lem1099685 _25287)). Qed.
Lemma lem1100052 {_25287 : Type'} : term2 _25287.
Proof. exact (@lem1100051 _25287 term3). Qed.
Lemma lem1100053 {_25287 : Type'} : (term2 _25287) = (term4 _25287).
Proof. exact (eq_refl (term2 _25287)). Qed.
Lemma lem1100054 {_25287 : Type'} : term4 _25287.
Proof. exact (EQ_MP (@lem1100053 _25287) (@lem1100052 _25287)). Qed.
Lemma lem1100055 {_25287 : Type'} (h1 : (@NULL _25287) = (term5 _25287)) : (@NULL _25287) = (term5 _25287).
Proof. exact (h1). Qed.
Lemma lem1100056 {_25287 : Type'} (h1 : (@NULL _25287) = (term5 _25287)) : (term5 _25287) = (@NULL _25287).
Proof. exact (SYM (@lem1100055 _25287 h1)). Qed.
Lemma lem1100057 {_25287 : Type'} (h1 : (term5 _25287) = (@NULL _25287)) : (term5 _25287) = (@NULL _25287).
Proof. exact (h1). Qed.
Lemma lem1100058 {_25287 : Type'} (h1 : (term5 _25287) = (@NULL _25287)) : (@NULL _25287) = (term5 _25287).
Proof. exact (SYM (@lem1100057 _25287 h1)). Qed.
Lemma lem1100059 {_25287 : Type'} : ((@NULL _25287) = (term5 _25287)) = ((term5 _25287) = (@NULL _25287)).
Proof. exact (prop_ext (fun h1 : (@NULL _25287) = (term5 _25287) => @lem1100056 _25287 h1) (fun h1 : (term5 _25287) = (@NULL _25287) => @lem1100058 _25287 h1)). Qed.
Lemma lem1100062 {_25287 : Type'} : (term5 _25287) = (@NULL _25287).
Proof. exact (EQ_MP (@lem1100059 _25287) (@lem1100049 _25287)). Qed.
Lemma lem1100063 {_25287 : Type'} : (term5 _25287) = (@NULL _25287).
Proof. exact (@lem1100062 _25287). Qed.
Lemma lem1100064 {_25287 : Type'} : (@nil _25287) = (@nil _25287).
Proof. exact (eq_refl (@nil _25287)). Qed.
Lemma lem1100065 {_25287 : Type'} : (term6 _25287) = (@NULL _25287 (@nil _25287)).
Proof. exact (MK_COMB (@lem1100063 _25287) (@lem1100064 _25287)). Qed.
Lemma lem1100066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100067 {_25287 : Type'} : (term7 _25287) = (term8 _25287).
Proof. exact (MK_COMB (@lem1100066) (@lem1100065 _25287)). Qed.
Lemma lem1100068 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem1100069 {_25287 : Type'} : ((term6 _25287) = True) = ((@NULL _25287 (@nil _25287)) = True).
Proof. exact (MK_COMB (@lem1100067 _25287) (@lem1100068)). Qed.
Lemma lem1100070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1100071 {_25287 : Type'} : (term9 _25287) = (term10 _25287).
Proof. exact (MK_COMB (@lem1100070) (@lem1100069 _25287)). Qed.
Lemma lem1100073 {_25287 : Type'} : (term5 _25287) = (@NULL _25287).
Proof. exact (EQ_MP (@lem1100059 _25287) (@lem1100049 _25287)). Qed.
Lemma lem1100074 {_25287 : Type'} : (term5 _25287) = (@NULL _25287).
Proof. exact (@lem1100073 _25287). Qed.
Lemma lem1100075 {_25287 : Type'} (h : _25287) (t : list _25287) : (@cons _25287 h t) = (@cons _25287 h t).
Proof. exact (eq_refl (@cons _25287 h t)). Qed.
Lemma lem1100076 {_25287 : Type'} (h : _25287) (t : list _25287) : (term11 _25287 h t) = (term12 _25287 h t).
Proof. exact (MK_COMB (@lem1100074 _25287) (@lem1100075 _25287 h t)). Qed.
Lemma lem1100077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100078 {_25287 : Type'} (h : _25287) (t : list _25287) : (term13 _25287 h t) = (term14 _25287 h t).
Proof. exact (MK_COMB (@lem1100077) (@lem1100076 _25287 h t)). Qed.
Lemma lem1100079 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1100080 {_25287 : Type'} (h : _25287) (t : list _25287) : ((term11 _25287 h t) = False) = ((term12 _25287 h t) = False).
Proof. exact (MK_COMB (@lem1100078 _25287 h t) (@lem1100079)). Qed.
Lemma lem1100081 {_25287 : Type'} (h : _25287) : (term15 _25287 h) = (term16 _25287 h).
Proof. exact (fun_ext (fun t : list _25287 => @lem1100080 _25287 h t)). Qed.
Lemma lem1100082 {_25287 : Type'} : (@all (list _25287)) = (@all (list _25287)).
Proof. exact (eq_refl (@all (list _25287))). Qed.
Lemma lem1100083 {_25287 : Type'} (h : _25287) : (term17 _25287 h) = (term18 _25287 h).
Proof. exact (MK_COMB (@lem1100082 _25287) (@lem1100081 _25287 h)). Qed.
Lemma lem1100084 {_25287 : Type'} : (term19 _25287) = (term20 _25287).
Proof. exact (fun_ext (fun h : _25287 => @lem1100083 _25287 h)). Qed.
Lemma lem1100085 {_25287 : Type'} : (@all _25287) = (@all _25287).
Proof. exact (eq_refl (@all _25287)). Qed.
Lemma lem1100086 {_25287 : Type'} : (term21 _25287) = (term22 _25287).
Proof. exact (MK_COMB (@lem1100085 _25287) (@lem1100084 _25287)). Qed.
Lemma lem1100087 {_25287 : Type'} : (term4 _25287) = (term23 _25287).
Proof. exact (MK_COMB (@lem1100071 _25287) (@lem1100086 _25287)). Qed.
Lemma lem1100088 {_25287 : Type'} : term23 _25287.
Proof. exact (EQ_MP (@lem1100087 _25287) (@lem1100054 _25287)). Qed.
Lemma lem1100089 {_25287 : Type'} : term22 _25287.
Proof. exact (proj2 (@lem1100088 _25287)). Qed.
Lemma lem1100090 {_25287 : Type'} : (@NULL _25287 (@nil _25287)) = True.
Proof. exact (proj1 (@lem1100088 _25287)). Qed.
Lemma lem1100091 {_25287 : Type'} (h : _25287) : term24 _25287 h.
Proof. exact (@lem1100089 _25287 h). Qed.
Lemma lem1100092 {_25287 : Type'} (h : _25287) : (term24 _25287 h) = (term18 _25287 h).
Proof. exact (eq_refl (term24 _25287 h)). Qed.
Lemma lem1100093 {_25287 : Type'} (h : _25287) : term18 _25287 h.
Proof. exact (EQ_MP (@lem1100092 _25287 h) (@lem1100091 _25287 h)). Qed.
Lemma lem1100094 {_25287 : Type'} (h : _25287) (t : list _25287) : term25 _25287 h t.
Proof. exact (@lem1100093 _25287 h t). Qed.
Lemma lem1100095 {_25287 : Type'} (h : _25287) (t : list _25287) : (term25 _25287 h t) = ((term12 _25287 h t) = False).
Proof. exact (eq_refl (term25 _25287 h t)). Qed.
Lemma lem1100096 {_25287 : Type'} (h : _25287) (t : list _25287) : (term12 _25287 h t) = False.
Proof. exact (EQ_MP (@lem1100095 _25287 h t) (@lem1100094 _25287 h t)). Qed.
Lemma lem1100097 {_25287 : Type'} (h : _25287) (t : list _25287) : term26 _25287 h t.
Proof. exact (conj (@lem1100090 _25287) (@lem1100096 _25287 h t)). Qed.
