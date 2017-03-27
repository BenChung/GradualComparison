using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace dyntest
{
    namespace Kafka
    {
        interface IA
        {
            IA m(IA x);
        }
        interface II
        {
            II m(IC x);
        }
        interface IT
        {
            IT s(II x);
            dynamic t(dynamic x);
        }
        interface IC
        {
            IC n(IC x);
        }
        class A : IA
        {
            public A()
            {

            }
            public IA m(IA x)
            {
                return this;
            }

        }
        class I : II
        {
            public I()
            {

            }
            public II m(IC x)
            {
                return this;
            }

        }
        class T : IT
        {
            public T()
            {

            }
            public IT s(II x)
            {
                return this;
            }

            public dynamic t(dynamic x)
            {
                return (dynamic)this.s((II)x);
            }

        }
        class C : IC
        {
            public C()
            {

            }
            public IC n(IC x)
            {
                return this;
            }

        }
        class Program
        {
            public static dynamic Main(string[] args)
            {
                return (dynamic)new T().t((dynamic)new A());
            }
        }
    }
}
