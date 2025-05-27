class B{
    int a;
    int b;
    B(int x)
    {
        a = x;
        b = 2*x;
    }

    B(int x, int y)
    {
        super();
        a = x;
        b = y;
    }
}


class A extends B{
    int c;
    int d;
    A(int x,int y)
    {
        super(x);
        c = x;
        d = y;
    }

    A(int x,int y,int z)
    {
        super(z,2*z);
        c = x;
        d = y;
    }

    public static void main(String[] args) {
        A o1 = new A(2,3);
        A o2 = new A(2,3,3);

        if(o1.equals(o2))
        {
            System.out.println("Objects are equal");
        }
        else
        {
            System.out.println("Objects are not equal");
        }
    }
}