class Example3 {
    int a;
    int b;
    String name;
    Example3()
    {
        a = 10;
        b = 20;
        name = "John";
    }  
    Example3(int x)
    {
        a = x;
    }
    Example3(int x,int y)
    {
        b = x;
        a = y;
    }
    Example3(int x, int y, String n)
    {
        a = x;
        b = y;
        name = n;
    }


    public static void main(String[] args) {
        
        System.out.println("hello");
    }
}
