import logging
from unittest import TestCase, expectedFailure

from autosledgi.isabelle.process_parser import IsabelleProcessingStatus
from autosledgi.isabelle.proof import Proof, PStatus
from tests import init_log, reset_log


class ProcessParserTest(TestCase):

    @classmethod
    def setUpClass(cls):
        cls.log = init_log(logging.INFO)

    @classmethod
    def tearDownClass(cls):
        reset_log()

    strings = [
        (
            'default apply script',
            'cvc4: Try this: by (metis Suc_length_conv assms) (31 ms)',
            {
                'prover': 'cvc4',
                'apply_proof': 'by (metis Suc_length_conv assms)',
                'apply_keyword': 'by',
                'apply_method': 'metis',
                'apply_time': '31',
                'apply_unit': 'ms'
            }
        ),
        (
            'default apply script that failed to measure its runtime within sledgehammers "preplay_timeout"',
            'cvc4: Try this: by (metis Suc_length_conv assms)',
            {
                'prover': 'cvc4',
                'apply_proof': 'by (metis Suc_length_conv assms)',
                'apply_keyword': 'by',
                'apply_method': 'metis',
                'apply_time': None,
                'apply_unit': None
            }
        ),
        (
            'default apply script with "using", no brackets, and different scale',
            'cvc4: Try this: using a apply b (66 s)',
            {
                'prover': 'cvc4',
                'apply_proof': 'using a apply b',
                'apply_keyword': 'apply',
                'apply_method': 'b',
                'apply_time': '66',
                'apply_unit': 's'
            }
        ),
        (
            'default apply script with explicit no ISAR proof',
            'cvc4: Try this: using a apply b (66 s)\n(No Isar proof available)',
            {
                'prover': 'cvc4',
                'apply_proof': 'using a apply b',
                'apply_keyword': 'apply',
                'apply_method': 'b',
                'apply_time': '66',
                'apply_unit': 's'
            }
        ),
        (
            'default apply script with explicit no ISAR proof and no preplay',
            'cvc4: Try this: using a apply b\n(No Isar proof available)',
            {
                'prover': 'cvc4',
                'apply_proof': 'using a apply b',
                'apply_keyword': 'apply',
                'apply_method': 'b',
                'apply_time': None,
                'apply_unit': None,
            }
        ),
        (
            'apply script and ISAR proof',
            'cvc4: Try this: using a apply b (31 ms)\n\nIsar proof (655 ms):\nproof -\n  assume "blabla"\n  have "∀l. l ≤ #⇩√" by blast\nqed',
            {
                'prover': 'cvc4',
                'apply_proof': 'using a apply b',
                'apply_keyword': 'apply',
                'apply_method': 'b',
                'apply_time': '31',
                'apply_unit': 'ms',
                'isar_proof': 'proof -\n  assume "blabla"\n  have "∀l. l ≤ #⇩√" by blast\nqed',
                'isar_time': '655',
                'isar_unit': 'ms'
            }
        ),
        (
            'ISAR with timeout',
            'cvc4: Try this: using a apply b (31 ms)\n\nIsar proof (> 1.0 s, timed out):\nproof -\n  assume "blabla"\n  have "∀l. l ≤ #⇩√" by blast\nqed',
            {
                'prover': 'cvc4',
                'apply_proof': 'using a apply b',
                'apply_keyword': 'apply',
                'apply_method': 'b',
                'apply_time': '31',
                'apply_unit': 'ms',
                'isar_proof': 'proof -\n  assume "blabla"\n  have "∀l. l ≤ #⇩√" by blast\nqed',
                'isar_time': None,
                'isar_unit': None
            }
        )
    ]

    def test_internal_methods(self):
        for explanation, str, expected in ProcessParserTest.strings:
            try:
                apply_res = IsabelleProcessingStatus().__get_apply_script_results__(str)
                isar_res = IsabelleProcessingStatus().__get_isar_results__(str)
                self.assertEqual(expected, apply_res | isar_res, msg=f'Failed for {explanation}')

            except AttributeError as e:
                raise Exception(f'Failed for {explanation}') from None

    def test_applyScript(self):
        t = IsabelleProcessingStatus()
        t.process('cvc4: Try this: by (metis Suc_length_conv assms) (31 ms)')

        self.assertEqual([Proof(prover='cvc4',
                                proof='by (metis Suc_length_conv assms)',
                                method='metis',
                                time=31,
                                is_done=True)],
                         t.get_proofs())

    def test_applyScriptWithoutTime(self):
        t = IsabelleProcessingStatus()
        t.process('cvc4: Try this: by (metis Suc_length_conv assms)')

        self.assertEqual([Proof(prover='cvc4',
                                proof='by (metis Suc_length_conv assms)',
                                method='metis',
                                time=None,
                                is_done=True)],
                         t.get_proofs())

    def test_applyScriptTimedOut(self):
        t = IsabelleProcessingStatus()
        t.process('cvc5: Try this:\n  by (metis lnsuc_lnle_emb min.absorb1 min.left_commute\n    nle_le) (> 1.0 s, timed out)')

        self.assertEqual([Proof(prover='cvc5',
                                proof='by (metis lnsuc_lnle_emb min.absorb1 min.left_commute\n    nle_le)',
                                method='metis',
                                time=None,
                                is_done=True)],
                         t.get_proofs())

    def test_applyScriptTimedOutNoIsar(self):
        t = IsabelleProcessingStatus()
        t.process('verit: Try this:\n  by (metis le_cases3 min.mono\n    min_absorb2) (> 1.0 s, timed out)\n(No Isar proof available)')

        self.assertEqual(['by (metis le_cases3 min.mono', '    min_absorb2)'], t.get_proofs()[0].get_proof())

    def test_applyScriptUsingMultiline(self):
        t = IsabelleProcessingStatus()
        t.process('cvc5: Try this:\n  using\n    ref_TelecommandAndTelemetry_LLR_rough_TelecommandAndTelemetry_HLR.refinement\n    by blast (13 ms)')

        self.assertEqual([Proof(prover='cvc5',
                                proof='using\n    ref_TelecommandAndTelemetry_LLR_rough_TelecommandAndTelemetry_HLR.refinement\n    by blast',
                                method='blast',
                                time=13,
                                is_done=True)],
                         t.get_proofs())

    def test_applyScriptNoIsar(self):
        t = IsabelleProcessingStatus()
        t.process(
            'zipperposition: Try this: using a b c by (metis d e f) (233 ms)\n(No Isar proof available)')

        self.assertEqual([Proof(prover='zipperposition',
                                proof='using a b c by (metis d e f)',
                                method='metis',
                                time=233,
                                is_done=True)],
                         t.get_proofs())

    def test_applyScriptWithIsar(self):
        t = IsabelleProcessingStatus()
        t.process(
            'p: Try this: apply (metis facts)\n\nIsar proof (> 1.0 s, timed out):\nproof -\n  show ?thesis by m\nqed')

        self.assertEqual(
            [
                Proof(prover='p',
                      proof='apply (metis facts)',
                      method='metis',
                      time=None,
                      is_done=False),
                Proof(prover='p',
                      proof='proof -\n  show ?thesis by m\nqed',
                      method='isar',
                      time=None,
                      is_done=True)
            ],
            t.get_proofs()
        )

    def test_multipleLines(self):
        t = IsabelleProcessingStatus()
        t.process('p: Try this: by metis')
        t.process('p2: Try this: by auto\n(No Isar proof available)')
        t.process('p: Try this: by auto (21 ms)\n\nIsar proof (> 1.0 s, timed out):\n proof rule\nshow c\nqed')

        self.assertEqual(4, len(t.get_proofs()), 'Should be four proofs')
        self.assertEqual(t.get_proofs()[3].method, 'isar', 'Last proof should have been the ISAR proof')

        t.process('p: Try this: by auto (21 ms)\n\nIsar proof (> 1.0 s, timed out):\n proof rule\nshow c\nnext')

        self.assertEqual(5, len(t.get_proofs()), 'Non-finished (non-qed) ISAR proofs should be ignored')
        self.assertEqual(t.get_proofs()[4].method, 'auto', 'Last proof should have been the auto proof')

    def test_workingLemma(self):

        msgs = ['Sledgehammering...',
                'cvc5 found a proof...',
                'cvc5 found a proof...',
                'e found a proof...',
                'vampire found a proof...',
                'spass found a proof...',
                'cvc5: Try this:\n  by (metis len_stream_def outputSubsetInput_after_bundlemergepred) (206 ms)',
                'verit found a proof...',
                'cvc5: Duplicate proof',
                'e: Try this:\n  by (metis len_stream_def outputSubsetInput_after_bundlemergepred) (262 ms)\n\nIsar proof (> 1.0 s, timed out):\nproof -\n  fix i :: "channels msgWithChan event stream" and g :: "channels msgWithChan event stream \\<rightarrow> channels\\<^sup>\\<Omega>"\n  assume a1: "spf \\<in> mergeTimed \\<then> eSem (eaut ())"\n  assume a2: "#\\<^sub>\\<surd> sb = #\\<^sub>\\<surd> i"\n  assume a3: "(\\<bbbW>) (sbgetter\\<cdot>sb)"\n  assume a4: "g \\<in> eSem (eaut ())"\n  assume a5: "uSplit\\<cdot>i \\<sqsubseteq> sb"\n  have "\\<forall>s c sa ca. eValues\\<cdot>(sbgetter\\<cdot>(c\\<cdot>s)) \\<subseteq> eValues\\<cdot>(channel_input_dataAbbr sa) \\<or> #\\<^sub>\\<surd> sa \\<noteq> #\\<^sub>\\<surd> s \\<or> slen\\<cdot>(channel_control_dataAbbr sa) \\<noteq> \\<infinity> \\<or> slen\\<cdot>(channel_input_dataAbbr sa) \\<noteq> \\<infinity> \\<or> \\<not> (\\<bbbW>) (sbgetter\\<cdot>sa) \\<or> uSplit\\<cdot>s \\<notsqsubseteq> sa \\<or> c \\<notin> eSem (eaut ()) \\<or> \\<not> 0 < slen\\<cdot> (esnth (esk1_3 sa c s)\\<cdot> (channel_input_dataAbbr sa)) \\<or> ca \\<notin> mergeTimed \\<then> eSem (eaut ())"\n    by (metis len_stream_def outputSubsetInput_after_bundlemergepred) (* > 1.0 s, timed out *)\n  then show "slen\\<cdot>(channel_input_dataAbbr sb) = \\<infinity> \\<and> slen\\<cdot>(channel_control_dataAbbr sb) = \\<infinity> \\<and> (\\<forall>n. 0 < slen\\<cdot> (esnth n\\<cdot>(channel_input_dataAbbr sb))) \\<longrightarrow> eValues\\<cdot>(sbgetter\\<cdot>(g\\<cdot>i)) \\<subseteq> eValues\\<cdot>(channel_input_dataAbbr sb)"\n    using a5 a4 a3 a2 a1 by blast\nqed',
                'spass: Try this:\n  by (metis len_stream_def outputSubsetInput_after_bundlemergepred) (205 ms)\n\nIsar proof (319 ms):\nproof -\n  fix i :: "channels msgWithChan event stream" and g :: "channels msgWithChan event stream \\<rightarrow> channels\\<^sup>\\<Omega>"\n  assume a1: "(\\<bbbW>) (sbgetter\\<cdot>sb)"\n  assume a2: "uSplit\\<cdot>i \\<sqsubseteq> sb"\n  assume a3: "#\\<^sub>\\<surd> sb = #\\<^sub>\\<surd> i"\n  assume a4: "g \\<in> eSem (eaut ())"\n  assume a5: "spf \\<in> mergeTimed \\<then> eSem (eaut ())"\n  have "g \\<in> eSem (eaut ()) \\<and> uSplit\\<cdot>i \\<sqsubseteq> sb"\n    using a4 a2 by meson\n  then show "slen\\<cdot>(channel_input_dataAbbr sb) = \\<infinity> \\<and> slen\\<cdot>(channel_control_dataAbbr sb) = \\<infinity> \\<and> (\\<forall>n. 0 < slen\\<cdot> (esnth n\\<cdot>(channel_input_dataAbbr sb))) \\<longrightarrow> eValues\\<cdot>(sbgetter\\<cdot>(g\\<cdot>i)) \\<subseteq> eValues\\<cdot>(channel_input_dataAbbr sb)"\n    using a5 a3 a1 by (metis (no_types) len_stream_def outputSubsetInput_after_bundlemergepred)\nqed',
                'vampire: Try this:\n  by (metis len_stream_def outputSubsetInput_after_bundlemergepred) (242 ms)\n(No Isar proof available)',
                'verit: Try this:\n  by (metis len_stream_def outputSubsetInput_after_bundlemergepred) (292 ms)\n\nIsar proof (478 ms):\nproof -\n  fix i :: "channels msgWithChan event stream" and g :: "channels msgWithChan event stream \\<rightarrow> channels\\<^sup>\\<Omega>"\n  assume a1: "spf \\<in> mergeTimed \\<then> eSem (eaut ())"\n  assume a2: "(\\<bbbW>) (sbgetter\\<cdot>sb)"\n  assume a3: "g \\<in> eSem (eaut ())"\n  assume a4: "uSplit\\<cdot>i \\<sqsubseteq> sb"\n  assume a5: "#\\<^sub>\\<surd> sb = #\\<^sub>\\<surd> i"\n  obtain nn :: nat where\n    "spf \\<in> mergeTimed \\<then> eSem (eaut ()) \\<and> (\\<bbbW>) (sbgetter\\<cdot>sb) \\<and> g \\<in> eSem (eaut ()) \\<and> uSplit\\<cdot>i \\<sqsubseteq> sb \\<and> #\\<^sub>\\<surd> sb = #\\<^sub>\\<surd> i \\<and> \\<infinity> = #(channel_input_dataAbbr sb) \\<and> \\<infinity> = #(channel_control_dataAbbr sb) \\<and> 0 < #(esnth nn\\<cdot>(channel_input_dataAbbr sb)) \\<longrightarrow> eValues\\<cdot>(sbgetter\\<cdot>(g\\<cdot>i)) \\<subseteq> eValues\\<cdot>(channel_input_dataAbbr sb)"\n    by (metis outputSubsetInput_after_bundlemergepred)\n  then show "slen\\<cdot>(channel_input_dataAbbr sb) = \\<infinity> \\<and> slen\\<cdot>(channel_control_dataAbbr sb) = \\<infinity> \\<and> (\\<forall>n. 0 < slen\\<cdot> (esnth n\\<cdot>(channel_input_dataAbbr sb))) \\<longrightarrow> eValues\\<cdot>(sbgetter\\<cdot>(g\\<cdot>i)) \\<subseteq> eValues\\<cdot>(channel_input_dataAbbr sb)"\n    using a5 a4 a3 a2 a1 by (simp add: len_stream_def)\nqed',
                'Done']

        parser = IsabelleProcessingStatus()
        for msg in msgs:
            parser.process(msg)

        self.assertTrue(parser.is_proof_found())

    def test_causalityLemma(self):

        msgs = ['Sledgehammering...',
                'cvc5 found a proof...',
                'spass found a proof...',
                'vampire found a proof...',
                'verit found a proof...',
                'zipperposition found a proof...',
                'zipperposition found a proof...',
                'e found a proof...',
                'cvc5: Try this:\n  apply (meson dual_order.trans lnsuc_lnle_emb min.cobounded1) (101 ms)',
                'vampire: Try this:\n  apply (meson lnsuc_lnle_emb min.cobounded1 order_trans) (74 ms)\n(No Isar proof available)',
                'verit: Try this:\n  apply (meson lnsuc_lnle_emb min.cobounded1 trans_lnle) (117 ms)\n\nIsar proof (50 ms):\nproof -\n  assume a1: "#\\<^sub>\\<surd> channel_input1_data_pattern <\\<^sup>l #\\<^sub>\\<surd> channel_scheduler1_output_data_pattern"\n  have "\\<forall>l la. min (l::lnat) la \\<le> l"\n    using min.cobounded1 by blast\n  then show "min (#\\<^sub>\\<surd> channel_input1_data_pattern) (min (#\\<^sub>\\<surd> channel_input2_data_pattern) (min (#\\<^sub>\\<surd> channel_input3_data_pattern) (#\\<^sub>\\<surd> channel_input4_data_pattern))) <\\<^sup>l #\\<^sub>\\<surd> channel_scheduler1_output_data_pattern"\n    using a1 lnsuc_lnle_emb trans_lnle by blast\nnext',
                'spass: Try this:\n  apply (metis inf_great leI lnle2le lnle_and_gt_inf(1)\n    min.bounded_iff) (360 ms)\n(No Isar proof available)',
                'e: Try this:\n  apply (metis\n    lnsuc_lnle_emb[of\n      "min (#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream))\n        (min (#\\<^sub>\\<surd> (channel_input2_data_pattern::Packet event stream))\n          (min (#\\<^sub>\\<surd> (channel_input3_data_pattern::Packet event stream))\n            (#\\<^sub>\\<surd> (channel_input4_data_pattern::Packet event stream))))"\n      "#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream)"]\n    min.assoc[of "#\\<^sub>\\<surd> (channel_output1_data_pattern::Packet event stream)"\n      "lnsuc\\<cdot>(#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream))"\n      "lnsuc\\<cdot>\n       (min (#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream))\n         (min (#\\<^sub>\\<surd> (channel_input2_data_pattern::Packet event stream))\n           (min (#\\<^sub>\\<surd> (channel_input3_data_pattern::Packet event stream))\n             (#\\<^sub>\\<surd> (channel_input4_data_pattern::Packet event stream)))))"]\n    min.cobounded2[of\n      "min (lnsuc\\<cdot>(#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream)))\n        (lnsuc\\<cdot>\n         (min (#\\<^sub>\\<surd> channel_input1_data_pattern)\n           (min (#\\<^sub>\\<surd> (channel_input2_data_pattern::Packet event stream))\n             (min (#\\<^sub>\\<surd> (channel_input3_data_pattern::Packet event stream))\n               (#\\<^sub>\\<surd> (channel_input4_data_pattern::Packet event stream))))))"\n      "#\\<^sub>\\<surd> (channel_output1_data_pattern::Packet event stream)"]\n    min.cobounded2[of\n      "min (#\\<^sub>\\<surd> (channel_input2_data_pattern::Packet event stream))\n        (min (#\\<^sub>\\<surd> (channel_input3_data_pattern::Packet event stream))\n          (#\\<^sub>\\<surd> (channel_input4_data_pattern::Packet event stream)))"\n      "#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream)"]\n    min.commute[of\n      "min (lnsuc\\<cdot>(#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream)))\n        (lnsuc\\<cdot>\n         (min (#\\<^sub>\\<surd> channel_input1_data_pattern)\n           (min (#\\<^sub>\\<surd> (channel_input2_data_pattern::Packet event stream))\n             (min (#\\<^sub>\\<surd> (channel_input3_data_pattern::Packet event stream))\n               (#\\<^sub>\\<surd> (channel_input4_data_pattern::Packet event stream))))))"\n      "#\\<^sub>\\<surd> (channel_output1_data_pattern::Packet event stream)"]\n    min.commute[of "#\\<^sub>\\<surd> (channel_output1_data_pattern::Packet event stream)"\n      "lnsuc\\<cdot>(#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream))"]\n    min.commute[of\n      "lnsuc\\<cdot>(#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream))"\n      "lnsuc\\<cdot>\n       (min (#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream))\n         (min (#\\<^sub>\\<surd> (channel_input2_data_pattern::Packet event stream))\n           (min (#\\<^sub>\\<surd> (channel_input3_data_pattern::Packet event stream))\n             (#\\<^sub>\\<surd> (channel_input4_data_pattern::Packet event stream)))))"]\n    min.commute[of\n      "min (#\\<^sub>\\<surd> (channel_input2_data_pattern::Packet event stream))\n        (min (#\\<^sub>\\<surd> (channel_input3_data_pattern::Packet event stream))\n          (#\\<^sub>\\<surd> (channel_input4_data_pattern::Packet event stream)))"\n      "#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream)"]\n    min.order_iff[of\n      "lnsuc\\<cdot>(#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream))"\n      "#\\<^sub>\\<surd> (channel_output1_data_pattern::Packet event stream)"]\n    min.order_iff[of\n      "lnsuc\\<cdot>\n       (min (#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream))\n         (min (#\\<^sub>\\<surd> (channel_input2_data_pattern::Packet event stream))\n           (min (#\\<^sub>\\<surd> (channel_input3_data_pattern::Packet event stream))\n             (#\\<^sub>\\<surd> (channel_input4_data_pattern::Packet event stream)))))"\n      "lnsuc\\<cdot>\n       (#\\<^sub>\\<surd> (channel_input1_data_pattern::Packet event stream))"]) (506 ms)\n\nIsar proof (114 ms):\nproof -\n  assume a1: "#\\<^sub>\\<surd> channel_input1_data_pattern <\\<^sup>l #\\<^sub>\\<surd> channel_scheduler1_output_data_pattern"\n  have "\\<forall>l la lb. min (l::lnat) (min la lb) \\<le> lb"\n    by (metis min.assoc min.cobounded2)\n  then have "\\<forall>l. min l (lnsuc\\<cdot>(#\\<^sub>\\<surd> channel_input1_data_pattern)) \\<le> #\\<^sub>\\<surd> channel_scheduler1_output_data_pattern"\n    using a1 by (metis (no_types) min.order_iff)\n  then show "min (#\\<^sub>\\<surd> channel_input1_data_pattern) (min (#\\<^sub>\\<surd> channel_input2_data_pattern) (min (#\\<^sub>\\<surd> channel_input3_data_pattern) (#\\<^sub>\\<surd> channel_input4_data_pattern))) <\\<^sup>l #\\<^sub>\\<surd> channel_scheduler1_output_data_pattern"\n    by (metis (no_types) lnsuc_lnle_emb min.cobounded2 min.commute min.order_iff)\nnext',
                'zipperposition: Try this:\n  apply (meson dual_order.trans lnsuc_lnle_emb min.bounded_iff\n    order_refl) (808 ms)\n(No Isar proof available)',
                'zipperposition: Try this:\n  apply (metis dual_order.trans less_lnsuc lnle2le lnsuc_le min.absorb_iff2\n    min.assoc min.cobounded2 min.commute min.idem min.left_commute\n    min.orderE min.strict_boundedE min.strict_coboundedI1\n    min.strict_order_iff min_less_iff_disj min_rek nle_le\n    verit_comp_simplify1(2) verit_la_disequality) (> 1.0 s, timed out)\n\nIsar proof (> 1.2 s, timed out):\nproof -\n  assume a1: "#\\<^sub>\\<surd> channel_input1_data_pattern <\\<^sup>l #\\<^sub>\\<surd> channel_scheduler1_output_data_pattern"\n  have f2: "\\<forall>l la. la = l \\<or> la \\<noteq> min l (lnsuc\\<cdot>la)"\n    using min_rek by blast\n  have f3: "\\<forall>l. l \\<le> lnsuc\\<cdot>l"\n    by fastforce\n  have f4: "\\<forall>l. min (l::lnat) l = l"\n    by simp\n  have f5: "\\<forall>l la lb. \\<not> (l::lnat) \\<le> la \\<or> lb \\<le> la \\<or> \\<not> lb \\<le> l"\n    using dual_order.trans by blast\n  have f6: "\\<forall>l la. (l::lnat) \\<le> la \\<or> la \\<le> l"\n    by force\n  have f7: "\\<forall>l la lb. min (la::lnat) (min l lb) = min l (min la lb)"\n    using min.left_commute by blast\n  have f8: "\\<forall>l la. min (la::lnat) l = min l la"\n    using min.commute by blast\n  have f9: "\\<forall>l la lb. min (min (l::lnat) la) lb = min l (min la lb)"\n    using min.assoc by blast\n  have f10: "\\<forall>l la. min (la::lnat) l = l \\<or> \\<not> l \\<le> la"\n    using min.absorb_iff2 by blast\n  have f11: "\\<forall>l la. (l::lnat) \\<le> la \\<or> min la l \\<noteq> l"\n    using min.absorb_iff2 by blast\n  have f12: "\\<forall>l la. min (l::lnat) la \\<le> la"\n    using min.cobounded2 by blast\n  have f13: "\\<forall>l la. (l::lnat) = min l la \\<or> \\<not> l \\<le> la"\n    by (metis (no_types) min.orderE)\n  have f14: "\\<forall>l la. l \\<le> la \\<or> \\<not> l < lnsuc\\<cdot>la"\n    using lnle2le by blast\n  have f15: "\\<forall>l la. lnsuc\\<cdot>l < lnsuc\\<cdot>la \\<or> \\<not> l < la"\n    using lnsuc_le by presburger\n  have f16: "\\<forall>l la lb. (l::lnat) < la \\<or> lb < la \\<or> \\<not> min l lb < la"\n    by linarith\n  have f17: "\\<forall>l la lb. (l::lnat) < la \\<or> \\<not> l < min lb la"\n    by simp\n  have f18: "\\<forall>l la. (la::lnat) \\<noteq> l \\<or> \\<not> la < l"\n    by fastforce\n  have f19: "\\<forall>l la. (l::lnat) < la \\<or> l = la \\<or> l \\<noteq> min l la"\n    using min.strict_order_iff by blast\n  have f20: "\\<forall>l la lb. \\<not> (l::lnat) < la \\<or> min l lb < la"\n    using min.strict_coboundedI1 by blast\n  have f21: "\\<forall>l. (l::lnat) \\<le> l"\n    by force\n  have "\\<forall>l la. \\<not> (l::lnat) \\<le> la \\<or> \\<not> la \\<le> l \\<or> l = la"\n    by simp\n  then show "min (#\\<^sub>\\<surd> channel_input1_data_pattern) (min (#\\<^sub>\\<surd> channel_input2_data_pattern) (min (#\\<^sub>\\<surd> channel_input3_data_pattern) (#\\<^sub>\\<surd> channel_input4_data_pattern))) <\\<^sup>l #\\<^sub>\\<surd> channel_scheduler1_output_data_pattern"\n    using f21 f20 f19 f18 f17 f16 f15 f14 f13 f12 f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 a1 by metis (* > 1.0 s, timed out *)\nnext',
                'Done']

        parser = IsabelleProcessingStatus()
        for msg in msgs:
            parser.process(msg)

        self.assertTrue(parser.is_proof_found())

    def test_capacity(self):
        msgs = ['Sledgehammering...',
                'cvc5 found a proof...',
                'cvc5: Try this:\n  by (metis controlMessageSemantics_after_bundlemergepred\n    def_Capacity_HLR3_Input.SB.getter_len\n    infManyOutputMessages_after_bundlemergepred len_stream_def\n    somechannotempty) (399 ms)',
                'cvc5 found a proof...',
                'cvc5: Duplicate proof',
                'spass found a proof...',
                'vampire found a proof...',
                'spass: Try this:\n  by (metis controlMessageSemantics_after_bundlemergepred\n    def_Capacity_HLR3_Input.SB.getter_len\n    infManyOutputMessages_after_bundlemergepred len_stream_def\n    somechannotempty) (468 ms)\n\nIsar proof (> 3.2 s, timed out):\nproof -\n  fix i :: "channels msgWithChan event stream" and g :: "channels msgWithChan event stream \\<rightarrow> channels\\<^sup>\\<Omega>"\n  assume a1: "(\\<bbbW>) (channel_input_dataAbbr sb)"\n  assume a2: "uSplit\\<cdot>i \\<sqsubseteq> sb"\n  assume a3: "#\\<^sub>\\<surd> sb = #\\<^sub>\\<surd> i"\n  assume a4: "g \\<in> eSem (eaut cap)"\n  assume a5: "spf \\<in> mergeTimed \\<then> eSem (eaut cap)"\n  { fix nn :: nat\n    have ff1: "\\<And>s. slen\\<cdot>(channel_input_dataAbbr s) = #s"\n      by (metis def_Capacity_HLR3_Input.SB.getter_len len_stream_def somechannotempty)\n    have ff2: "\\<forall>s n. \\<exists>p. \\<forall>c ca sa na cb cc sb nb. (\\<not> Packet_get_size p < n \\<or> c \\<notin> mergeTimed \\<then> eSem (eaut n) \\<or> ca \\<notin> eSem (eaut n) \\<or> #\\<^sub>\\<surd> s \\<noteq> #\\<^sub>\\<surd> sa \\<or> uSplit\\<cdot>sa \\<notsqsubseteq> s \\<or> \\<not> (\\<bbbW>) (channel_input_dataAbbr s) \\<or> #s \\<noteq> \\<infinity> \\<or> #(esnth (Suc na)\\<cdot>(fst (sbgetter\\<cdot>(ca\\<cdot>sa)))) = #(esnth na\\<cdot>(channel_input_dataAbbr s)) \\<or> NAK \\<in> sValues\\<cdot> (esnth (Suc na)\\<cdot> (fst (sbgetter\\<cdot>(ca\\<cdot>sa))))) \\<and> (cb \\<notin> mergeTimed \\<then> eSem (eaut n) \\<or> cc \\<notin> eSem (eaut n) \\<or> #\\<^sub>\\<surd> s \\<noteq> #\\<^sub>\\<surd> sb \\<or> uSplit\\<cdot>sb \\<notsqsubseteq> s \\<or> \\<not> (\\<bbbW>) (channel_input_dataAbbr s) \\<or> #s \\<noteq> \\<infinity> \\<or> p \\<in> eValues\\<cdot>(channel_input_dataAbbr s) \\<or> #(esnth (Suc nb)\\<cdot>(fst (sbgetter\\<cdot>(cc\\<cdot>sb)))) = #(esnth nb\\<cdot>(channel_input_dataAbbr s)) \\<or> NAK \\<in> sValues\\<cdot> (esnth (Suc nb)\\<cdot>(fst (sbgetter\\<cdot>(cc\\<cdot>sb)))))"\n      by (metis controlMessageSemantics_after_bundlemergepred)\n    have "\\<forall>s. \\<exists>n. \\<forall>na. \\<exists>p. \\<forall>c ca sa cb cc sb sc. (\\<not> Packet_get_size p < na \\<or> c \\<notin> mergeTimed \\<then> eSem (eaut na) \\<or> ca \\<notin> eSem (eaut na) \\<or> \\<not> (\\<bbbW>) (channel_input_dataAbbr s) \\<or> uSplit\\<cdot>sa \\<notsqsubseteq> s \\<or> #\\<^sub>\\<surd> s \\<noteq> #\\<^sub>\\<surd> sa \\<or> #(channel_input_dataAbbr s) \\<noteq> \\<infinity> \\<or> \\<not> 0 < #(esnth n\\<cdot>(channel_input_dataAbbr s)) \\<or> #(e2ustream\\<cdot>(snd (sbgetter\\<cdot>(ca\\<cdot>sa)))) = \\<infinity>) \\<and> (cb \\<notin> mergeTimed \\<then> eSem (eaut na) \\<or> cc \\<notin> eSem (eaut na) \\<or> \\<not> (\\<bbbW>) (channel_input_dataAbbr sb) \\<or> uSplit\\<cdot>sc \\<notsqsubseteq> sb \\<or> #\\<^sub>\\<surd> sb \\<noteq> #\\<^sub>\\<surd> sc \\<or> #(channel_input_dataAbbr sb) \\<noteq> \\<infinity> \\<or> \\<not> 0 < #(esnth n\\<cdot> (channel_input_dataAbbr sb)) \\<or> p \\<in> eValues\\<cdot>(channel_input_dataAbbr sb) \\<or> #(e2ustream\\<cdot>(snd (sbgetter\\<cdot>(cc\\<cdot>sc)))) = \\<infinity>)"\n      by (metis infManyOutputMessages_after_bundlemergepred) (* > 1.0 s, timed out *)\n    then have "\\<exists>p n na. slen\\<cdot>(channel_input_dataAbbr sb) \\<noteq> \\<infinity> \\<or> p \\<in> eValues\\<cdot>(channel_input_dataAbbr sb) \\<and> \\<not> Packet_get_size p < cap \\<or> slen\\<cdot>(e2ustream\\<cdot>(snd (sbgetter\\<cdot>(g\\<cdot>i)))) = \\<infinity> \\<or> NAK \\<in> sValues\\<cdot> (esnth (Suc nn)\\<cdot>(fst (sbgetter\\<cdot>(g\\<cdot>i)))) \\<and> \\<not> 0 < slen\\<cdot>(esnth n\\<cdot>(channel_input_dataAbbr sb)) \\<or> slen\\<cdot>(esnth (Suc nn)\\<cdot>(fst (sbgetter\\<cdot>(g\\<cdot>i)))) = slen\\<cdot>(esnth nn\\<cdot>(channel_input_dataAbbr sb)) \\<and> \\<not> 0 < slen\\<cdot>(esnth na\\<cdot>(channel_input_dataAbbr sb))"\n      using ff2 ff1 a5 a4 a3 a2 a1 by (metis (full_types) len_stream_def) }\n  then have "\\<forall>n. \\<exists>p na nb. slen\\<cdot>(channel_input_dataAbbr sb) \\<noteq> \\<infinity> \\<or> p \\<in> eValues\\<cdot>(channel_input_dataAbbr sb) \\<and> \\<not> Packet_get_size p < cap \\<or> slen\\<cdot>(e2ustream\\<cdot>(snd (sbgetter\\<cdot>(g\\<cdot>i)))) = \\<infinity> \\<or> NAK \\<in> sValues\\<cdot> (esnth (Suc n)\\<cdot>(fst (sbgetter\\<cdot>(g\\<cdot>i)))) \\<and> \\<not> 0 < slen\\<cdot> (esnth na\\<cdot>(channel_input_dataAbbr sb)) \\<or> slen\\<cdot>(esnth (Suc n)\\<cdot>(fst (sbgetter\\<cdot>(g\\<cdot>i)))) = slen\\<cdot>(esnth n\\<cdot>(channel_input_dataAbbr sb)) \\<and> \\<not> 0 < slen\\<cdot>(esnth nb\\<cdot>(channel_input_dataAbbr sb))"\n    by fastforce\n  then show "slen\\<cdot>(channel_input_dataAbbr sb) = \\<infinity> \\<and> (\\<forall>p\\<in>eValues\\<cdot>(channel_input_dataAbbr sb). Packet_get_size p < cap) \\<and> ((\\<forall>n. slen\\<cdot>(esnth (Suc n)\\<cdot>(fst (sbgetter\\<cdot>(g\\<cdot>i)))) = slen\\<cdot>(esnth n\\<cdot>(channel_input_dataAbbr sb)) \\<or> NAK \\<in> sValues\\<cdot> (esnth (Suc n)\\<cdot> (fst (sbgetter\\<cdot>(g\\<cdot>i))))) \\<longrightarrow> (\\<forall>n. 0 < slen\\<cdot> (esnth n\\<cdot>(channel_input_dataAbbr sb)))) \\<longrightarrow> slen\\<cdot>(e2ustream\\<cdot>(snd (sbgetter\\<cdot>(g\\<cdot>i)))) = \\<infinity>"\n    by blast\nqed',
                'vampire: Try this:\n  by (metis controlMessageSemantics_after_bundlemergepred\n    def_Capacity_HLR3_Input.SB.getter_len\n    infManyOutputMessages_after_bundlemergepred len_stream_def\n    somechannotempty) (2.0 s)\n\nIsar proof (> 4.5 s, timed out):\nproof -\n  fix i :: "channels msgWithChan event stream" and g :: "channels msgWithChan event stream \\<rightarrow> channels\\<^sup>\\<Omega>"\n  assume a1: "spf \\<in> mergeTimed \\<then> eSem (eaut cap)"\n  assume a2: "(\\<bbbW>) (channel_input_dataAbbr sb)"\n  assume a3: "g \\<in> eSem (eaut cap)"\n  assume a4: "uSplit\\<cdot>i \\<sqsubseteq> sb"\n  assume a5: "#\\<^sub>\\<surd> sb = #\\<^sub>\\<surd> i"\n  obtain nn :: "channels\\<^sup>\\<Omega> \\<Rightarrow> nat" where\n    f6: "\\<forall>X4. (\\<exists>X5. \\<not> 0 < #(esnth X5\\<cdot> (channel_input_dataAbbr X4))) \\<longrightarrow> \\<not> 0 < #(esnth (nn X4)\\<cdot>(channel_input_dataAbbr X4))"\n    by moura\n  obtain pp :: "nat \\<Rightarrow> channels\\<^sup>\\<Omega> \\<Rightarrow> Packet" where\n    f7: "\\<forall>X3 X4. (\\<exists>X6. X6 \\<in> eValues\\<cdot>(channel_input_dataAbbr X4) \\<and> \\<not> Packet_get_size X6 < X3) \\<longrightarrow> pp X3 X4 \\<in> eValues\\<cdot>(channel_input_dataAbbr X4) \\<and> \\<not> Packet_get_size (pp X3 X4) < X3"\n    by moura\n  obtain ppa :: "channels\\<^sup>\\<Omega> \\<Rightarrow> nat \\<Rightarrow> Packet" where\n    f8: "\\<forall>X1 X4. (\\<exists>X5. X5 \\<in> eValues\\<cdot>(channel_input_dataAbbr X1) \\<and> \\<not> Packet_get_size X5 < X4) \\<longrightarrow> ppa X1 X4 \\<in> eValues\\<cdot>(channel_input_dataAbbr X1) \\<and> \\<not> Packet_get_size (ppa X1 X4) < X4"\n    by moura\n  have "\\<forall>c s ca n sa. (\\<exists>n. \\<not> 0 < #(esnth n\\<cdot>(channel_input_dataAbbr sa))) \\<or> (\\<exists>p. p \\<in> eValues\\<cdot>(channel_input_dataAbbr sa) \\<and> \\<not> Packet_get_size p < n) \\<or> c \\<notin> eSem (eaut n) \\<or> \\<not> (\\<bbbW>) (channel_input_dataAbbr sa) \\<or> ca \\<notin> mergeTimed \\<then> eSem (eaut n) \\<or> #\\<^sub>\\<surd> s \\<noteq> #\\<^sub>\\<surd> sa \\<or> uSplit\\<cdot>s \\<notsqsubseteq> sa \\<or> \\<infinity> \\<noteq> #(channel_input_dataAbbr sa) \\<or> \\<infinity> = #(e2ustream\\<cdot>(snd (sbgetter\\<cdot>(c\\<cdot>s))))"\n    by (metis (no_types) infManyOutputMessages_after_bundlemergepred)\n  then obtain nna :: "channels\\<^sup>\\<Omega> \\<Rightarrow> nat" and ppb :: "nat \\<Rightarrow> channels\\<^sup>\\<Omega> \\<Rightarrow> Packet" where\n    f9: "\\<forall>c s ca n sa. \\<not> 0 < #(esnth (nna sa)\\<cdot>(channel_input_dataAbbr sa)) \\<or> ppb n sa \\<in> eValues\\<cdot>(channel_input_dataAbbr sa) \\<and> \\<not> Packet_get_size (ppb n sa) < n \\<or> c \\<notin> eSem (eaut n) \\<or> \\<not> (\\<bbbW>) (channel_input_dataAbbr sa) \\<or> ca \\<notin> mergeTimed \\<then> eSem (eaut n) \\<or> #\\<^sub>\\<surd> s \\<noteq> #\\<^sub>\\<surd> sa \\<or> uSplit\\<cdot>s \\<notsqsubseteq> sa \\<or> \\<infinity> \\<noteq> #(channel_input_dataAbbr sa) \\<or> \\<infinity> = #(e2ustream\\<cdot>(snd (sbgetter\\<cdot>(c\\<cdot>s))))"\n    using f7 f6 by moura (* > 1.0 s, timed out *)\n  obtain ppc :: "channels\\<^sup>\\<Omega> \\<Rightarrow> nat \\<Rightarrow> Packet" where\n    f10: "\\<forall>c s ca sa n. #s \\<noteq> \\<infinity> \\<or> #\\<^sub>\\<surd> s \\<noteq> #\\<^sub>\\<surd> sa \\<or> \\<not> (\\<bbbW>) (channel_input_dataAbbr s) \\<or> c \\<notin> eSem (eaut n) \\<or> ca \\<notin> mergeTimed \\<then> eSem (eaut n) \\<or> ppc s n \\<in> eValues\\<cdot>(channel_input_dataAbbr s) \\<and> \\<not> Packet_get_size (ppc s n) < n \\<or> (\\<forall>n. #(esnth n\\<cdot>(channel_input_dataAbbr s)) = #(esnth (Suc n)\\<cdot>(fst (sbgetter\\<cdot>(c\\<cdot>sa)))) \\<or> NAK \\<in> sValues\\<cdot> (esnth (Suc n)\\<cdot> (fst (sbgetter\\<cdot>(c\\<cdot>sa))))) \\<or> uSplit\\<cdot>sa \\<notsqsubseteq> s"\n    using f8 by (metis (no_types) controlMessageSemantics_after_bundlemergepred)\n  moreover\n  { assume "Packet_get_size (ppc sb cap) < cap"\n    moreover\n    { assume "\\<exists>n. \\<not> 0 < slen\\<cdot>(esnth n\\<cdot>(channel_input_dataAbbr sb)) \\<and> Packet_get_size (ppc sb cap) < cap"\n      then have "\\<infinity> = #sb \\<longrightarrow> (\\<exists>n. \\<not> 0 < slen\\<cdot> (esnth n\\<cdot>(channel_input_dataAbbr sb))) \\<and> (NAK \\<in> sValues\\<cdot> (esnth (Suc sK0)\\<cdot>(fst (sbgetter\\<cdot>(g\\<cdot>i)))) \\<or> slen\\<cdot>(esnth (Suc sK0)\\<cdot>(fst (sbgetter\\<cdot>(g\\<cdot>i)))) = slen\\<cdot>(esnth sK0\\<cdot>(channel_input_dataAbbr sb))) \\<or> \\<infinity> \\<noteq> slen\\<cdot>(channel_input_dataAbbr sb) \\<or> \\<infinity> = slen\\<cdot>(e2ustream\\<cdot>(snd (sbgetter\\<cdot>(g\\<cdot>i)))) \\<or> (\\<exists>p. p \\<in> eValues\\<cdot>(channel_input_dataAbbr sb) \\<and> \\<not> Packet_get_size p < cap)"\n        using f10 a5 a4 a3 a2 a1 by (metis len_stream_def) }\n    ultimately have "\\<infinity> = #sb \\<longrightarrow> ((\\<exists>n. \\<not> 0 < slen\\<cdot> (esnth n\\<cdot>(channel_input_dataAbbr sb))) \\<and> (NAK \\<in> sValues\\<cdot> (esnth (Suc sK0)\\<cdot>(fst (sbgetter\\<cdot>(g\\<cdot>i)))) \\<or> slen\\<cdot>(esnth (Suc sK0)\\<cdot>(fst (sbgetter\\<cdot>(g\\<cdot>i)))) = slen\\<cdot>(esnth sK0\\<cdot>(channel_input_dataAbbr sb))) \\<or> \\<infinity> \\<noteq> slen\\<cdot>(channel_input_dataAbbr sb) \\<or> \\<infinity> = slen\\<cdot>(e2ustream\\<cdot>(snd (sbgetter\\<cdot>(g\\<cdot>i)))) \\<or> (\\<exists>p. p \\<in> eValues\\<cdot>(channel_input_dataAbbr sb) \\<and> \\<not> Packet_get_size p < cap)) \\<or> (\\<exists>s. 0 < slen\\<cdot>(esnth (nna s)\\<cdot>(channel_input_dataAbbr s)) \\<and> Packet_get_size (ppb cap s) < cap \\<and> #\\<^sub>\\<surd> i = #\\<^sub>\\<surd> s \\<and> \\<infinity> = slen\\<cdot>(channel_input_dataAbbr s) \\<and> (\\<bbbW>) (channel_input_dataAbbr s) \\<and> uSplit\\<cdot>i \\<sqsubseteq> s) \\<or> (\\<exists>s. 0 < slen\\<cdot>(esnth (nna s)\\<cdot>(channel_input_dataAbbr s)) \\<and> ppb cap s \\<notin> eValues\\<cdot>(channel_input_dataAbbr s) \\<and> uSplit\\<cdot>i \\<sqsubseteq> s \\<and> #\\<^sub>\\<surd> i = #\\<^sub>\\<surd> s \\<and> \\<infinity> = slen\\<cdot>(channel_input_dataAbbr s) \\<and> (\\<bbbW>) (channel_input_dataAbbr s))"\n      using a5 a4 a2 by (metis (no_types)) }\n  ultimately show "slen\\<cdot>(channel_input_dataAbbr sb) = \\<infinity> \\<and> (\\<forall>p\\<in>eValues\\<cdot>(channel_input_dataAbbr sb). Packet_get_size p < cap) \\<and> ((\\<forall>n. slen\\<cdot>(esnth (Suc n)\\<cdot>(fst (sbgetter\\<cdot>(g\\<cdot>i)))) = slen\\<cdot>(esnth n\\<cdot>(channel_input_dataAbbr sb)) \\<or> NAK \\<in> sValues\\<cdot> (esnth (Suc n)\\<cdot> (fst (sbgetter\\<cdot>(g\\<cdot>i))))) \\<longrightarrow> (\\<forall>n. 0 < slen\\<cdot> (esnth n\\<cdot>(channel_input_dataAbbr sb)))) \\<longrightarrow> slen\\<cdot>(e2ustream\\<cdot>(snd (sbgetter\\<cdot>(g\\<cdot>i)))) = \\<infinity>"\n    using f9 a5 a4 a3 a2 a1 by (metis (full_types) def_Capacity_HLR3_Input.SB.getter_len len_stream_def somechannotempty)\nqed',
                'Done']

        parser = IsabelleProcessingStatus()
        for msg in msgs:
            parser.process(msg)

        self.assertTrue(parser.is_proof_found())
        self.assertTrue(sorted(parser.get_proofs())[0].prover == 'cvc5')
