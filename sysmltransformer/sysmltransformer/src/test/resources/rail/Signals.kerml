classifier Signal specializes Base::Anything 
            unions Enters unions OpenUp unions SetColor;

abstract datatype MyMap {

    datatype K;
    datatype V;

    behavior get {
        in key: K;
        out value: V;
    }
}