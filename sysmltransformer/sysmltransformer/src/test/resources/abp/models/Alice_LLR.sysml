part def Alice_LLR specializes Alice_HLR{
  timing delayed;

    port input: ~Data;
    port control: ~Booleans;
    port output: Data_Bool_Tuples;

    attribute init_ctrl: boolean;

    #tsyn exhibit state AliceAutomaton {

        entry action {
            assign ctrl := init_ctrl;
            assign buffer := new List<String>();
        }

        attribute ctrl: boolean;
        attribute buffer: List<String>;

        state EmptyBuf;
        state SingleBuf;
        state MultiBuf;

        then EmptyBuf;

        transition
            first EmptyBuf
            accept input.val
            do action {
                send (input.val, ctrl) to output.val;
                assign ctrl := ctrl;
                assign buffer := new List<nat>(input.val);
            }
            then SingleBuf;

        transition
            first EmptyBuf
            accept Eps
            do action {
                send Eps to output.val;
                assign ctrl := ctrl;
                assign buffer := buffer;
            }
            then EmptyBuf;

        transition
            first SingleBuf
            accept control.val
            if control.val == ctrl
            do action {
                send Eps to output.val;
                assign ctrl := not ctrl;
                assign buffer := buffer.tail();
            }
            then EmptyBuf;

        transition
            first SingleBuf
            accept input.val
            if control.val == ctrl
            do action {
                send (input.val, not ctrl) to output.val;
                assign ctrl := not ctrl;
                assign buffer := new List<nat>(input.val);
            }
            then SingleBuf;

        transition
            first SingleBuf
            accept control.val
            if control.val == ctrl
            do action {
                send (input.val, not ctrl) to output.val;
                assign ctrl := not ctrl;
                assign buffer := new List<nat>(input.val);
            }
            then SingleBuf;

        transition
            first SingleBuf
            accept Eps
            do action {
                send (buffer.head(), ctrl) to output.val;
                assign ctrl := ctrl;
                assign buffer := buffer;
            }
            then SingleBuf;

        transition
            first SingleBuf
            accept input.val
            do action {
                send (input.val, ctrl) to output.val;
                assign ctrl := ctrl;
                assign buffer := buffer.append(new List<String>(input.val));
            }
            then MultiBuf;

        transition
            first MultiBuf
            accept Eps
            do action {
                assign ctrl := ctrl;
                assign buffer := buffer;
                send (buffer.head(), ctrl) to output.val;
            }
            then MultiBuf;

        transition
            first MultiBuf
            accept control.val
            if control.val == ctrl and buffer.count() > 2
            do action {
                send Eps to output.val;
                assign ctrl := not ctrl;
                assign buffer := buffer.tail();
            }
            then MultiBuf;

        transition
            first MultiBuf
            accept control.val
            if control.val == ctrl and buffer.count() == 2
            do action {
                send Eps to output.val;
                assign ctrl := not ctrl;
                assign buffer := buffer.tail();
            }
            then SingleBuf;

        transition
            first MultiBuf
            accept input.val
            do action {
                assign ctrl := ctrl;
                assign buffer := buffer.append(new List<String>(input.val));
                send (buffer.head(), ctrl) to output.val;
            }
            then MultiBuf;

        transition
            first MultiBuf
            accept control.val
            if control.val == ctrl
            do action {
                assign ctrl := not ctrl;
                assign buffer := buffer.tail().append(new List<String>(input.val));
                send (buffer.tail().head(), not ctrl) to output.val;
            }
            then MultiBuf;

        transition
            first MultiBuf
            accept input.val
            if control.val == ctrl
            do action {
                assign ctrl := not ctrl;
                assign buffer := buffer.tail().append(new List<String>(input.val));
                send (buffer.tail().head(), not ctrl) to output.val;
            }
            then MultiBuf;
    }
}
