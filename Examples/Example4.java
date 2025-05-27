class A {
    int c;

    A(int a) {
        super();
        c = a;
    }
}

class Example4 extends A {
    int a;
    int b;

    Example4(int a, int b) {
        super(a);
        this.a = a;
        this.b = b;
    }

    public static void main(String[] args) {
        for(int i=0;i<100000;++i)
        {
        	for(int j=i;j<100000;++j) {
        		Example4 obj = new Example4(3,4);
        	}
        }
    }
}
