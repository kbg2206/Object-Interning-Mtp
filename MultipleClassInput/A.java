


public class A extends B{
    int a;
    A(int x,int y,int z,int w)
    {
        super(y,z,w);
        a=x;
        System.out.println("A constructor called ");
    }

    public static void main(String[] args) {
        A o1 = new A(1,2,3,4);
        A o2 = new A(1,2,3,4);

        if(o1.equals(o2)){
            System.out.println("Objects are equal");
        }
        else{
            System.out.println("Objects are not equal");
        }
    }
}
